
#include <iostream>
#include <iomanip>
#include <string>
#include <vector>
#include <unordered_map>
#include <map>
#include <chrono>
#include <cmath>
#include <algorithm>
#include <fstream>
#include <sstream>
#include <random>
#include <cstdlib>
#include <functional>
#include <cctype>
using namespace std;
using namespace std::chrono;
static const double MAX_PAX    = 300.0;  // connecting passengers at which factor C saturates at 100
static const double WINDOW_MIN = 60.0;   // minutes: window used by T (schedule urgency) and W (waiting)
static const double WT_EMERG = 0.40, WT_FUEL = 0.25, WT_SCHED = 0.15, WT_PAX = 0.10, WT_WAIT = 0.10;
static bool useColor = true;
static const char* C_RED    = "\033[1;31m";
static const char* C_GREEN  = "\033[1;32m";
static const char* C_YELLOW = "\033[1;33m";
static const char* C_CYAN   = "\033[1;36m";
static const char* C_BOLD   = "\033[1m";
static string clr(const char* c) { return useColor ? string(c) : string(); }
static string rst() { return clr("\033[0m"); }
static string trim(const string& s) {
    size_t b = s.find_first_not_of(" \t\r\n");
    if (b == string::npos) return "";
    size_t e = s.find_last_not_of(" \t\r\n");
    return s.substr(b, e - b + 1);
}
static string upper(string s) { for (auto& c : s) c = (char)toupper((unsigned char)c); return s; }
static string lower(string s) { for (auto& c : s) c = (char)tolower((unsigned char)c); return s; }

static bool parseInt(const string& s, int& v) {
    if (s.empty()) return false;
    try {
        size_t p = 0;
        long x = stol(s, &p);
        if (p != s.size() || x < -1000000 || x > 1000000) return false;
        v = (int)x;
        return true;
    } catch (...) { return false; }
}
steady_clock::time_point simStart;   // captured ONCE in main()
double simScale  = 3.0;              // simulated minutes per real second (0 = frozen clock)
double simOffset = 0.0;              // extra minutes added by "Advance Simulation Clock"
double getCurrentTime() {
    double elapsedSec = duration<double>(steady_clock::now() - simStart).count();
    return elapsedSec * simScale + simOffset;
}
int nowCeil() { return (int)ceil(getCurrentTime() - 1e-9); }

string fmtTime(int m) {              // "HH:MM" of elapsed simulation time
    string sign = m < 0 ? "-" : "";
    m = abs(m);
    ostringstream o;
    o << sign << setfill('0') << setw(2) << (m / 60) << ":" << setw(2) << (m % 60);
    return o.str();
}
ofstream logFile;
void logEvent(const string& msg) {
    if (logFile.is_open()) logFile << "[" << fmtTime((int)getCurrentTime()) << "] " << msg << "\n";
}
struct Aircraft {
    string flightno;                 // unique identity (key of the heap's position map)
    string flighttype;               // "Heavy" / "Medium" / "Light"
    string operationtype;            // "Landing" / "Takeoff"
    int    scheduledtime        = 0; // planned time, sim-minutes since session start
    int    fuellevel            = 100;   // percent
    bool   emergencystatus      = false; // declared manually (menu 6)
    int    connectingpassengers = 0;
    int    runwayrequirements   = 0;     // minimum runway length in metres
    int    arrivaltime          = 0;     // when it entered the system
    int    waitingtime          = 0;     // minutes waited so far
    double priorityscore        = 0.0;
};
void calculatePriority(Aircraft& a) {
    double now = getCurrentTime();

    double E = a.emergencystatus ? 100 : 0;
    double F = 100 - a.fuellevel;                       // low fuel => high urgency

    double T;                                           // schedule urgency
    double delta = a.scheduledtime - now;
    if (delta <= 0)                 T = 100;            // due or overdue
    else if (delta >= WINDOW_MIN)   T = 0;              // far away
    else                            T = 100 * (1 - delta / WINDOW_MIN);

    double C = min((double)a.connectingpassengers, MAX_PAX) / MAX_PAX * 100;

    double waited = max(0.0, now - a.arrivaltime);      // waiting-time factor
    a.waitingtime = (int)waited;
    double W = min(waited, WINDOW_MIN) / WINDOW_MIN * 100;

    a.priorityscore = WT_EMERG * E + WT_FUEL * F + WT_SCHED * T + WT_PAX * C + WT_WAIT * W;
}
int typeIndex(const string& t) { return t == "Heavy" ? 0 : (t == "Medium" ? 1 : 2); }
static const int sepBase[3][3] = {   // minutes: previous (row) -> next (column); H, M, L
    {3, 4, 5},
    {2, 2, 4},
    {2, 2, 2}
};
static const char*  weatherName[5]   = {"", "Clear", "Light rain", "Thunderstorm", "Severe storm"};
static const double weatherFactors[5] = {1.0, 1.0, 1.25, 1.5, 2.0};
int    weatherLevel  = 1;
double weatherFactor = 1.0;          // multiplies separation AND operation duration

int sepMin(int prev, int next) { return (int)ceil(sepBase[prev][next] * weatherFactor - 1e-9); }
int opDuration()               { return (int)ceil(1.0 * weatherFactor - 1e-9); }
int defaultRunwayReq(const string& type) { return type == "Heavy" ? 3000 : (type == "Medium" ? 2200 : 1500); }
class IndexedMaxHeap {
    vector<Aircraft> heap;
    unordered_map<string, int> pos;

    void swapNodes(int i, int j) {
        swap(heap[i], heap[j]);
        pos[heap[i].flightno] = i;
        pos[heap[j].flightno] = j;
    }
    void siftUp(int i) {
        while (i > 0) {
            int p = (i - 1) / 2;
            if (higher(heap[i], heap[p])) { swapNodes(i, p); i = p; }
            else break;
        }
    }
    void siftDown(int i) {
        int n = (int)heap.size();            // int (not size_t) => no unsigned underflow
        while (true) {
            int l = 2 * i + 1, r = 2 * i + 2, best = i;
            if (l < n && higher(heap[l], heap[best])) best = l;
            if (r < n && higher(heap[r], heap[best])) best = r;
            if (best == i) break;
            swapNodes(i, best);
            i = best;
        }
    }
public:
    static bool higher(const Aircraft& a, const Aircraft& b) {
        if (fabs(a.priorityscore - b.priorityscore) > 1e-9) return a.priorityscore > b.priorityscore;
        if (a.scheduledtime != b.scheduledtime) return a.scheduledtime < b.scheduledtime;
        return a.flightno < b.flightno;
    }
    bool empty() const { return heap.empty(); }
    int  size()  const { return (int)heap.size(); }
    bool contains(const string& id) const { return pos.count(id) > 0; }
    bool get(const string& id, Aircraft& out) const {
        auto it = pos.find(id);
        if (it == pos.end()) return false;
        out = heap[it->second];
        return true;
    }
    bool insert(const Aircraft& a) {                       // O(log n)
        if (contains(a.flightno)) return false;
        heap.push_back(a);
        int i = (int)heap.size() - 1;
        pos[a.flightno] = i;
        siftUp(i);
        return true;
    }
    bool peekMax(Aircraft& out) const {                    // O(1)
        if (heap.empty()) return false;
        out = heap[0];
        return true;
    }
    bool extractMax(Aircraft& out) {                       // O(log n)
        if (heap.empty()) return false;                    // empty-heap safety
        out = heap[0];
        pos.erase(out.flightno);
        if (heap.size() == 1) { heap.pop_back(); return true; }
        heap[0] = heap.back();                             // last element goes to the root
        heap.pop_back();
        pos[heap[0].flightno] = 0;
        siftDown(0);
        return true;
    }
    // increaseKey / decreaseKey in one function: replace the record, then let it float UP
    // (priority increased) or sink DOWN (priority decreased). Only one of the two moves it.
    bool updateKey(const Aircraft& a) {                    // O(log n)
        auto it = pos.find(a.flightno);
        if (it == pos.end()) return false;
        int i = it->second;
        heap[i] = a;
        siftUp(i);
        siftDown(pos[a.flightno]);
        return true;
    }
    vector<string> ids() const {
        vector<string> v;
        for (auto& a : heap) v.push_back(a.flightno);
        return v;
    }
    vector<Aircraft> orderedSnapshot() const {             // heap-sort a COPY (heap itself untouched)
        IndexedMaxHeap tmp = *this;
        vector<Aircraft> out;
        Aircraft a;
        while (tmp.extractMax(a)) out.push_back(a);
        return out;
    }
    bool validate() const {                                // used by the self tests
        int n = (int)heap.size();
        if ((int)pos.size() != n) return false;
        for (int i = 0; i < n; i++) {
            auto it = pos.find(heap[i].flightno);
            if (it == pos.end() || it->second != i) return false;       // position map consistent
            if (i > 0 && higher(heap[i], heap[(i - 1) / 2])) return false; // heap property
        }
        return true;
    }
};
struct RunwayEntry { int runwayId = 0; int freeAt = 0; int version = 0; };

class RunwayMinHeap {
    vector<RunwayEntry> h;
    static bool lt(const RunwayEntry& a, const RunwayEntry& b) {
        if (a.freeAt != b.freeAt) return a.freeAt < b.freeAt;
        return a.runwayId < b.runwayId;
    }
    void siftUp(int i) {
        while (i > 0) {
            int p = (i - 1) / 2;
            if (lt(h[i], h[p])) { swap(h[i], h[p]); i = p; } else break;
        }
    }
    void siftDown(int i) {
        int n = (int)h.size();
        while (true) {
            int l = 2 * i + 1, r = 2 * i + 2, m = i;
            if (l < n && lt(h[l], h[m])) m = l;
            if (r < n && lt(h[r], h[m])) m = r;
            if (m == i) break;
            swap(h[i], h[m]);
            i = m;
        }
    }
public:
    void push(const RunwayEntry& e) { h.push_back(e); siftUp((int)h.size() - 1); }   // O(log R)
    bool peek(RunwayEntry& out) const { if (h.empty()) return false; out = h[0]; return true; }
    bool pop(RunwayEntry& out) {                                                     // O(log R)
        if (h.empty()) return false;
        out = h[0];
        h[0] = h.back();
        h.pop_back();
        if (!h.empty()) siftDown(0);
        return true;
    }
    bool   empty() const { return h.empty(); }
    size_t size()  const { return h.size(); }
};

class AircraftQueue {
    vector<Aircraft> data;
    size_t head = 0;
public:
    void enqueue(const Aircraft& a) { data.push_back(a); }                     // O(1)
    bool dequeue(Aircraft& out) {                                              // O(1) amortised
        if (head >= data.size()) return false;
        out = data[head++];
        if (head > 32 && head * 2 > data.size()) {                             // occasional compaction
            data.erase(data.begin(), data.begin() + (long)head);
            head = 0;
        }
        return true;
    }
    bool   empty() const { return head >= data.size(); }
    size_t size()  const { return data.size() - head; }
    Aircraft* find(const string& id) {
        for (size_t i = head; i < data.size(); ++i) if (data[i].flightno == id) return &data[i];
        return nullptr;
    }
    const Aircraft& at(size_t i) const { return data[head + i]; }
};
struct Runway {
    int  id = 0;
    int  length = 0;          // metres
    bool isOpen = true;
    int  freeAt = 0;          // minute when the last operation has finished
    bool hasLast = false;     // has this runway handled an operation yet?
    int  lastStart = 0;       // start minute of the last operation
    int  lastType = 0;        // 0 Heavy, 1 Medium, 2 Light
    int  version = 0;         // bumped whenever its heap entry must be invalidated
};

struct ScheduledOp {
    Aircraft ac;              // copy of the aircraft as it was scheduled
    int runwayId = 0;
    int start    = 0;
    int dur      = 1;
    int reqGap   = 0;         // separation required after the previous op on this runway
    int waited   = 0;         // start - arrivaltime
};

static void printAircraftHeader() {
    cout << left << setw(4) << "#" << setw(9) << "Flight" << setw(8) << "Type" << setw(9) << "Op"
         << setw(6) << "Fuel" << setw(7) << "Emerg" << setw(6) << "Pax" << setw(8) << "RwyReq"
         << setw(8) << "Sched" << "Priority\n";
}
static void printAircraftRow(int n, const Aircraft& a) {
    if (a.emergencystatus) cout << clr(C_RED);
    cout << left << setw(4) << n << setw(9) << a.flightno << setw(8) << a.flighttype
         << setw(9) << a.operationtype << setw(6) << (to_string(a.fuellevel) + "%")
         << setw(7) << (a.emergencystatus ? "YES" : "no") << setw(6) << a.connectingpassengers
         << setw(8) << a.runwayrequirements << setw(8) << fmtTime(a.scheduledtime)
         << fixed << setprecision(1) << a.priorityscore << rst() << "\n";
}

class AirportSystem {
public:                                   // public on purpose: keeps the self tests short
    AircraftQueue     incoming;           // arrivals not yet prioritised
    IndexedMaxHeap    waiting;            // prioritised, waiting for a runway
    vector<Runway>    runways;
    RunwayMinHeap     rheap;              // runway availability
    vector<ScheduledOp> schedule;         // every assigned operation (history + future)
    int conflictsResolved = 0;

    Runway& rw(int id) { return runways[id - 1]; }
    const Runway& rw(int id) const { return runways[id - 1]; }

    // ---------------- setup ----------------
    void addRunway(int length) {
        Runway r;
        r.id = (int)runways.size() + 1;
        r.length = length;
        runways.push_back(r);
        rheap.push({r.id, 0, r.version});
    }
    void initDefaultRunways() { addRunway(3600); addRunway(3000); addRunway(2200); }

    bool flightExists(const string& id) {
        if (incoming.find(id) || waiting.contains(id)) return true;
        for (auto& op : schedule) if (op.ac.flightno == id) return true;
        return false;
    }

    // ---------------- intake ----------------
    void addAircraft(Aircraft a) {
        a.arrivaltime = (int)floor(getCurrentTime());
        calculatePriority(a);
        incoming.enqueue(a);                                   // step 1: arrival queue
        logEvent("ARRIVAL " + a.flightno + " " + a.flighttype + " " + a.operationtype);
    }
    void drainIncoming() {                                     // queue -> priority heap
        Aircraft a;
        while (incoming.dequeue(a)) { calculatePriority(a); waiting.insert(a); }
    }
    void refreshPriorities() {                                 // time has passed: scores change
        for (const string& id : waiting.ids()) {               // ids() is a copy => safe while heap reorders
            Aircraft a;
            if (waiting.get(id, a)) { calculatePriority(a); waiting.updateKey(a); }
        }
    }

    void refreshRunwayEntry(int id) {                          // invalidate old entry, push a fresh one
        Runway& r = rw(id);
        r.version++;
        if (r.isOpen) rheap.push({r.id, r.freeAt, r.version});
    }
    void recomputeTail(Runway& r) {                            // rebuild "last op" info from the schedule
        const ScheduledOp* last = nullptr;
        for (auto& op : schedule)
            if (op.runwayId == r.id && (!last || op.start > last->start)) last = &op;
        if (last) {
            r.hasLast = true; r.lastStart = last->start;
            r.lastType = typeIndex(last->ac.flighttype);
            r.freeAt = last->start + last->dur;
        } else { r.hasLast = false; r.lastStart = 0; r.freeAt = 0; }
    }

    struct Choice { int runwayId = -1; int start = 0; int gap = 0; };

    bool pickRunway(const Aircraft& a, int nowI, Choice& best) {
        vector<RunwayEntry> examined;
        bool found = false;
        int aType = typeIndex(a.flighttype);
        RunwayEntry top;
        while (rheap.peek(top)) {
            Runway& r = rw(top.runwayId);
            if (!r.isOpen || top.version != r.version) { rheap.pop(top); continue; }  // lazy deletion
            if (found && top.freeAt >= best.start) break;                              // cannot improve
            rheap.pop(top);
            examined.push_back(top);
            if (r.length < a.runwayrequirements) continue;                             // too short
            int gap = r.hasLast ? sepMin(r.lastType, aType) : 0;                       // separation rule
            int s = max(nowI, r.freeAt);
            if (r.hasLast) s = max(s, r.lastStart + gap);                              // earliest safe time
            if (!found || s < best.start) { best.runwayId = r.id; best.start = s; best.gap = gap; found = true; }
        }
        for (auto& e : examined)                                                        // put back unchanged ones
            if (!(found && e.runwayId == best.runwayId)) rheap.push(e);
        return found;
    }

    void assignOp(const Aircraft& a, const Choice& c, int nowI) {
        Runway& r = rw(c.runwayId);
        ScheduledOp op;
        op.ac = a; op.runwayId = r.id; op.start = c.start; op.dur = opDuration(); op.reqGap = c.gap;
        op.waited = max(0, c.start - a.arrivaltime);
        schedule.push_back(op);
        r.hasLast = true; r.lastStart = c.start; r.lastType = typeIndex(a.flighttype);
        r.freeAt = c.start + op.dur;
        refreshRunwayEntry(r.id);                              // runway goes back with its NEW free time
        if (c.start > nowI) conflictsResolved++;               // wanted "now", separation/occupancy delayed it
        logEvent("SCHEDULED " + a.flightno + " " + a.operationtype + " R" + to_string(r.id) +
                 " at " + fmtTime(c.start) + " priority " + to_string((int)a.priorityscore) +
                 " wait " + to_string(op.waited));
    }
    int runSchedulingRound(bool print = true) {
        drainIncoming();
        refreshPriorities();
        int nowI = nowCeil();
        vector<ScheduledOp> made;
        vector<Aircraft> deferred;
        Aircraft a;
        while (waiting.extractMax(a)) {                        // highest priority first
            Choice c;
            if (pickRunway(a, nowI, c)) { assignOp(a, c, nowI); made.push_back(schedule.back()); }
            else deferred.push_back(a);                        // no open compatible runway
        }
        for (auto& d : deferred) waiting.insert(d);            // stay in the waiting pool
        if (print) printRound(made, deferred);
        return (int)made.size();
    }
    int cancelFutureOps(int runwayId) {
        double now = getCurrentTime();
        vector<ScheduledOp> keep, cancelled;
        for (auto& op : schedule) {
            bool match = (runwayId == -1 || op.runwayId == runwayId);
            if (op.start > now && match) cancelled.push_back(op); else keep.push_back(op);
        }
        schedule = keep;
        for (auto& op : cancelled) waiting.insert(op.ac);
        for (auto& r : runways)
            if (runwayId == -1 || r.id == runwayId) { recomputeTail(r); refreshRunwayEntry(r.id); }
        return (int)cancelled.size();
    }
    void closeRunway(int id) {
        if (id < 1 || id > (int)runways.size()) { cout << "No such runway.\n"; return; }
        Runway& r = rw(id);
        if (!r.isOpen) { cout << "Runway R" << id << " is already closed.\n"; return; }
        r.isOpen = false;                                      // lazy deletion: heap entry dies when popped
        int n = cancelFutureOps(id);
        conflictsResolved += n;
        logEvent("RUNWAY R" + to_string(id) + " CLOSED, " + to_string(n) + " operation(s) re-planned");
        cout << clr(C_YELLOW) << "Runway R" << id << " CLOSED. " << n << " planned operation(s) returned to the waiting heap."
             << rst() << "\n";
        runSchedulingRound();
    }
    void reopenRunway(int id) {
        if (id < 1 || id > (int)runways.size()) { cout << "No such runway.\n"; return; }
        Runway& r = rw(id);
        if (r.isOpen) { cout << "Runway R" << id << " is already open.\n"; return; }
        r.isOpen = true;
        recomputeTail(r);
        refreshRunwayEntry(id);                                // fresh heap entry with a new version
        logEvent("RUNWAY R" + to_string(id) + " REOPENED");
        cout << clr(C_GREEN) << "Runway R" << id << " REOPENED." << rst() << "\n";
        runSchedulingRound();
    }
    void setWeather(int level) {
        if (level == weatherLevel) { cout << "Weather is already \"" << weatherName[level] << "\".\n"; return; }
        weatherLevel = level;
        weatherFactor = weatherFactors[level];
        int n = cancelFutureOps(-1);
        logEvent(string("WEATHER -> ") + weatherName[level] + ", " + to_string(n) + " operation(s) re-planned");
        cout << clr(C_YELLOW) << "Weather: " << weatherName[level] << " (separation/duration x" << weatherFactor
             << "). " << n << " planned operation(s) re-planned." << rst() << "\n";
        runSchedulingRound();
    }

    enum Loc { NOT_FOUND, IN_QUEUE, IN_HEAP, SCHED_FUTURE, SCHED_DONE };
    Loc locate(const string& id) {
        if (incoming.find(id)) return IN_QUEUE;
        if (waiting.contains(id)) return IN_HEAP;
        double now = getCurrentTime();
        for (auto& op : schedule)
            if (op.ac.flightno == id) return op.start > now ? SCHED_FUTURE : SCHED_DONE;
        return NOT_FOUND;
    }
    bool modifyWaiting(const string& id, const function<void(Aircraft&)>& f) {
        if (Aircraft* p = incoming.find(id)) { f(*p); calculatePriority(*p); return true; }
        Aircraft a;
        if (waiting.get(id, a)) { f(a); calculatePriority(a); waiting.updateKey(a); return true; }
        return false;
    }
    int rankOf(const string& id) const {
        auto v = waiting.orderedSnapshot();
        for (size_t i = 0; i < v.size(); i++) if (v[i].flightno == id) return (int)i + 1;
        return 0;
    }

    void reportEmergency(const string& id) {
        Loc loc = locate(id);
        if (loc == NOT_FOUND)   { cout << "Flight " << id << " not found.\n"; return; }
        if (loc == SCHED_DONE)  { cout << "Flight " << id << " has already operated.\n"; return; }
        if (loc == SCHED_FUTURE) {                             // its slot is cancelled so it can jump ahead
            int n = cancelFutureOps(-1);
            cout << "Planned slot cancelled; " << n << " future operation(s) returned to the waiting heap for re-planning.\n";
        }
        int before = rankOf(id);
        modifyWaiting(id, [](Aircraft& a) { a.emergencystatus = true; });
        int after = rankOf(id);
        logEvent("EMERGENCY declared by " + id);
        cout << clr(C_RED) << "EMERGENCY declared for " << id << "." << rst();
        if (before && after) cout << " Heap updateKey: position " << before << " -> " << after << ".";
        cout << "\n";
        runSchedulingRound();
    }
    void delayFlight(const string& id, int minutes) {
        Loc loc = locate(id);
        if (loc == NOT_FOUND)  { cout << "Flight " << id << " not found.\n"; return; }
        if (loc == SCHED_DONE) { cout << "Flight " << id << " has already operated.\n"; return; }
        if (loc == SCHED_FUTURE) cancelFutureOps(-1);
        int before = rankOf(id);
        modifyWaiting(id, [minutes](Aircraft& a) { a.scheduledtime += minutes; });
        int after = rankOf(id);
        logEvent("DELAY " + id + " by " + to_string(minutes) + " min");
        cout << "Flight " << id << " delayed by " << minutes << " min.";
        if (before && after) cout << " Heap updateKey: position " << before << " -> " << after << ".";
        cout << "\n";
        runSchedulingRound();
    }

    // ---------------- views ----------------
    void printRound(vector<ScheduledOp> made, const vector<Aircraft>& deferred) const {
        if (made.empty() && deferred.empty()) { cout << "No aircraft waiting - nothing to schedule.\n"; return; }
        sort(made.begin(), made.end(), [](const ScheduledOp& a, const ScheduledOp& b) {
            return a.start != b.start ? a.start < b.start : a.runwayId < b.runwayId; });
        cout << "\n" << clr(C_BOLD) << "RUNWAY SCHEDULE (this round)" << rst() << "\n";
        cout << left << setw(8) << "Time" << setw(9) << "Flight" << setw(8) << "Type" << setw(11) << "Operation"
             << setw(8) << "Runway" << setw(10) << "Priority" << "Wait\n";
        double totalWait = 0;
        for (auto& op : made) {
            if (op.ac.emergencystatus) cout << clr(C_RED);
            cout << left << setw(8) << fmtTime(op.start) << setw(9) << op.ac.flightno << setw(8) << op.ac.flighttype
                 << setw(11) << op.ac.operationtype << setw(8) << ("R" + to_string(op.runwayId))
                 << setw(10) << fixed << setprecision(1) << op.ac.priorityscore << op.waited << " min" << rst() << "\n";
            totalWait += op.waited;
        }
        if (!made.empty())
            cout << "Scheduled " << made.size() << " operation(s), average wait this round "
                 << fixed << setprecision(1) << totalWait / made.size() << " min.\n";
        for (auto& d : deferred)
            cout << clr(C_YELLOW) << "DEFERRED " << d.flightno << ": needs a " << d.runwayrequirements
                 << " m runway and no open runway is long enough (stays in the waiting heap)." << rst() << "\n";
    }

    void printWaiting() const {
        cout << "\n" << clr(C_BOLD) << "ARRIVAL QUEUE (FIFO, not yet prioritised): " << incoming.size() << rst() << "\n";
        if (!incoming.empty()) {
            printAircraftHeader();
            for (size_t i = 0; i < incoming.size(); i++) printAircraftRow((int)i + 1, incoming.at(i));
        }
        cout << "\n" << clr(C_BOLD) << "WAITING HEAP (highest priority first): " << waiting.size() << rst() << "\n";
        if (waiting.empty()) cout << "No aircraft waiting.\n";
        else {
            printAircraftHeader();
            int n = 1;
            for (auto& a : waiting.orderedSnapshot()) printAircraftRow(n++, a);
        }
    }

    void printRunways() const {
        cout << "\n" << clr(C_BOLD) << "RUNWAY STATUS" << rst() << "  (weather: " << weatherName[weatherLevel]
             << ", separation/duration x" << weatherFactor << ")\n";
        cout << left << setw(8) << "Runway" << setw(10) << "Length" << setw(9) << "Status" << setw(11) << "Next free"
             << setw(10) << "Last op" << "Ops\n";
        static const char* tn[3] = {"Heavy", "Medium", "Light"};
        for (auto& r : runways) {
            int ops = 0;
            for (auto& op : schedule) if (op.runwayId == r.id) ops++;
            cout << clr(r.isOpen ? C_GREEN : C_RED);
            cout << left << setw(8) << ("R" + to_string(r.id)) << setw(10) << (to_string(r.length) + " m")
                 << setw(9) << (r.isOpen ? "OPEN" : "CLOSED")
                 << setw(11) << (r.hasLast ? fmtTime(r.freeAt) : string("-"))
                 << setw(10) << (r.hasLast ? tn[r.lastType] : "-") << ops << rst() << "\n";
        }
    }

    void printOperations() const {
        if (schedule.empty()) { cout << "No operations scheduled yet.\n"; return; }
        auto v = schedule;
        sort(v.begin(), v.end(), [](const ScheduledOp& a, const ScheduledOp& b) {
            return a.start != b.start ? a.start < b.start : a.runwayId < b.runwayId; });
        double now = getCurrentTime();
        cout << "\n" << clr(C_BOLD) << "TODAY'S OPERATIONS" << rst() << "  (clock now " << fmtTime((int)now) << ")\n";
        cout << left << setw(8) << "Time" << setw(9) << "Flight" << setw(8) << "Type" << setw(11) << "Operation"
             << setw(8) << "Runway" << setw(10) << "Priority" << setw(10) << "Wait" << "Status\n";
        for (auto& op : v) {
            bool done = op.start <= now;
            if (op.ac.emergencystatus) cout << clr(C_RED);
            cout << left << setw(8) << fmtTime(op.start) << setw(9) << op.ac.flightno << setw(8) << op.ac.flighttype
                 << setw(11) << op.ac.operationtype << setw(8) << ("R" + to_string(op.runwayId))
                 << setw(10) << fixed << setprecision(1) << op.ac.priorityscore
                 << setw(10) << (to_string(op.waited) + " min") << (done ? "DONE" : "PLANNED") << rst() << "\n";
        }
    }

    void printMetrics() const {
        cout << "\n" << clr(C_BOLD) << "PERFORMANCE ANALYSIS" << rst() << "\n";
        if (schedule.empty()) { cout << "No operations scheduled yet.\n"; }
        else {
            double now = getCurrentTime();
            double sumWait = 0; int maxWait = -1; string maxFlight; int emerg = 0, done = 0;
            for (auto& op : schedule) {
                sumWait += op.waited;
                if (op.waited > maxWait) { maxWait = op.waited; maxFlight = op.ac.flightno; }
                if (op.ac.emergencystatus) emerg++;
                if (op.start <= now) done++;
            }
            // utilisation: time a runway is reserved (operation + required separation) / its active window
            double totalBusy = 0, totalWindow = 0;
            vector<pair<int, double>> perRunway;
            for (auto& r : runways) {
                vector<ScheduledOp> v;
                for (auto& op : schedule) if (op.runwayId == r.id) v.push_back(op);
                if (v.empty()) continue;
                sort(v.begin(), v.end(), [](const ScheduledOp& a, const ScheduledOp& b) { return a.start < b.start; });
                double busy = 0;
                for (size_t i = 0; i < v.size(); i++) {
                    if (i + 1 < v.size()) {
                        int gap = v[i + 1].start - v[i].start;
                        busy += min(gap, max(v[i + 1].reqGap, v[i].dur));
                    } else busy += v[i].dur;
                }
                double window = v.back().start + v.back().dur - v.front().start;
                perRunway.push_back({r.id, window > 0 ? 100.0 * busy / window : 100.0});
                totalBusy += busy; totalWindow += window;
            }
            cout << fixed << setprecision(1);
            cout << "Average Waiting Time    : " << sumWait / schedule.size() << " min\n";
            cout << "Maximum Waiting Time    : " << maxWait << " min (" << maxFlight << ")\n";
            cout << "Runway Utilization      : " << (totalWindow > 0 ? 100.0 * totalBusy / totalWindow : 0.0) << " %\n";
            for (auto& p : perRunway) cout << "   R" << p.first << "                   : " << p.second << " %\n";
            cout << "Conflicts Resolved      : " << conflictsResolved << "\n";
            cout << "Emergency Flights       : " << emerg << "\n";
            cout << "Operations Scheduled    : " << schedule.size() << "  (completed so far: " << done << ")\n";
        }
        cout << "Still waiting           : " << waiting.size() + (int)incoming.size() << "\n";
    }

    void printTimeline() const {
        if (schedule.empty()) { cout << "No operations scheduled yet.\n"; return; }
        int tmin = 1 << 30, tmax = -(1 << 30);
        for (auto& op : schedule) { tmin = min(tmin, op.start); tmax = max(tmax, op.start + op.dur); }
        int span = tmax - tmin, width = min(span, 100);
        cout << "\n" << clr(C_BOLD) << "RUNWAY TIMELINE" << rst()
             << "  (1 char = 1 sim-minute;  L landing, T takeoff, E emergency, . free/separation)\n";
        if (span > width) cout << "(showing the first " << width << " minutes)\n";
        cout << string(12, ' ');
        for (int i = 0; i < width; i += 10) cout << left << setw(10) << fmtTime(tmin + i);
        cout << "\n";
        for (auto& r : runways) {
            vector<string> cells((size_t)width, ".");
            for (auto& op : schedule) {
                if (op.runwayId != r.id) continue;
                for (int k = 0; k < op.dur; k++) {
                    int idx = op.start + k - tmin;
                    if (idx < 0 || idx >= width) continue;
                    if (op.ac.emergencystatus) cells[(size_t)idx] = clr(C_RED) + "E" + rst();
                    else if (op.ac.operationtype == "Landing") cells[(size_t)idx] = clr(C_CYAN) + "L" + rst();
                    else cells[(size_t)idx] = clr(C_YELLOW) + "T" + rst();
                }
            }
            ostringstream p; p << "R" << r.id << " " << r.length << "m";
            cout << left << setw(12) << p.str();
            for (auto& c : cells) cout << c;
            if (!r.isOpen) cout << "  " << clr(C_RED) << "(CLOSED)" << rst();
            cout << "\n";
        }
    }

    // ---------------- CSV ----------------
    bool exportSchedule(const string& fn) const {
        ofstream out(fn);
        if (!out) return false;
        auto v = schedule;
        sort(v.begin(), v.end(), [](const ScheduledOp& a, const ScheduledOp& b) {
            return a.start != b.start ? a.start < b.start : a.runwayId < b.runwayId; });
        out << "start,flight,type,operation,runway,priority,emergency,waited_min\n";
        for (auto& op : v)
            out << fmtTime(op.start) << "," << op.ac.flightno << "," << op.ac.flighttype << "," << op.ac.operationtype
                << ",R" << op.runwayId << "," << fixed << setprecision(1) << op.ac.priorityscore << ","
                << (op.ac.emergencystatus ? 1 : 0) << "," << op.waited << "\n";
        return true;
    }

    static vector<string> splitCSV(const string& line) {
        vector<string> f; string cur; stringstream ss(line);
        while (getline(ss, cur, ',')) f.push_back(trim(cur));
        return f;
    }
    // columns: flightno,type,operation,fuel,emergency,pax,runway_req,minutes_from_now
    bool parseRow(const vector<string>& f, Aircraft& a, string& err) {
        if (f.size() != 8) { err = "expected 8 columns"; return false; }
        a.flightno = upper(f[0]);
        if (a.flightno.size() < 2 || a.flightno.size() > 8) { err = "bad flight number"; return false; }
        string t = lower(f[1]);
        if (t == "heavy" || t == "h") a.flighttype = "Heavy";
        else if (t == "medium" || t == "m") a.flighttype = "Medium";
        else if (t == "light" || t == "l") a.flighttype = "Light";
        else { err = "type must be Heavy/Medium/Light"; return false; }
        string o = lower(f[2]);
        if (o == "landing" || o == "l") a.operationtype = "Landing";
        else if (o == "takeoff" || o == "t") a.operationtype = "Takeoff";
        else { err = "operation must be Landing/Takeoff"; return false; }
        int fuel, em, pax, req, mins;
        string e = lower(f[4]);
        if (e == "1" || e == "yes" || e == "y" || e == "true") em = 1;
        else if (e == "0" || e == "no" || e == "n" || e == "false") em = 0;
        else { err = "emergency must be 0/1"; return false; }
        if (!parseInt(f[3], fuel) || fuel < 0 || fuel > 100) { err = "fuel must be 0-100"; return false; }
        if (!parseInt(f[5], pax) || pax < 0 || pax > 1000) { err = "pax must be 0-1000"; return false; }
        if (!parseInt(f[6], req) || req < 500 || req > 6000) { err = "runway_req must be 500-6000"; return false; }
        if (!parseInt(f[7], mins) || mins < -120 || mins > 720) { err = "minutes_from_now must be -120..720"; return false; }
        if (flightExists(a.flightno)) { err = "flight number already in system"; return false; }
        a.fuellevel = fuel; a.emergencystatus = em == 1; a.connectingpassengers = pax;
        a.runwayrequirements = req; a.scheduledtime = nowCeil() + mins;
        return true;
    }
    int importAircraft(const string& fn) {                    // returns number imported, -1 if file missing
        ifstream in(fn);
        if (!in) return -1;
        string line; int ok = 0, bad = 0, lineNo = 0;
        while (getline(in, line)) {
            lineNo++;
            line = trim(line);
            if (line.empty() || line[0] == '#') continue;
            auto f = splitCSV(line);
            if (!f.empty() && lower(f[0]) == "flightno") continue;      // header row
            Aircraft a; string err;
            if (parseRow(f, a, err)) { addAircraft(a); ok++; }
            else { cout << "  line " << lineNo << " skipped: " << err << "\n"; bad++; }
        }
        cout << "Imported " << ok << " aircraft, skipped " << bad << ".\n";
        return ok;
    }
};

// ============================================================================
// 7. CONSOLE INPUT HELPERS
// ============================================================================
static string readLine() {
    string s;
    if (!getline(cin, s)) { cout << "\n(input closed - exiting)\n"; exit(0); }
    return trim(s);
}
static int readInt(const string& prompt, int lo, int hi, bool hasDef = false, int def = 0) {
    while (true) {
        cout << prompt;
        string s = readLine();
        if (s.empty() && hasDef) return def;
        int v;
        if (parseInt(s, v) && v >= lo && v <= hi) return v;
        cout << "  Please enter a whole number between " << lo << " and " << hi << ".\n";
    }
}
static bool readYesNo(const string& prompt) {
    while (true) {
        cout << prompt << " (y/n): ";
        string s = lower(readLine());
        if (s == "y" || s == "yes") return true;
        if (s == "n" || s == "no") return false;
        cout << "  Please answer y or n.\n";
    }
}
static string readFlightNo(const string& prompt, AirportSystem& sys, bool mustExist) {
    while (true) {
        cout << prompt;
        string s = upper(readLine());
        bool ok = s.size() >= 2 && s.size() <= 8;
        for (char c : s) if (!isalnum((unsigned char)c)) ok = false;
        if (!ok) { cout << "  Flight numbers are 2-8 letters/digits (e.g. AI204).\n"; continue; }
        bool exists = sys.flightExists(s);
        if (mustExist && !exists) { cout << "  Flight " << s << " not found.\n"; continue; }
        if (!mustExist && exists) { cout << "  Flight " << s << " is already in the system.\n"; continue; }
        return s;
    }
}

static mt19937 rng(random_device{}());
static int rnd(int lo, int hi) { return uniform_int_distribution<int>(lo, hi)(rng); }

static Aircraft makeRandomAircraft(AirportSystem& sys) {
    static const char* airlines[] = {"AI", "EK", "6E", "SQ", "BA", "UA", "QR", "LH"};
    Aircraft a;
    do { a.flightno = string(airlines[rnd(0, 7)]) + to_string(rnd(100, 999)); } while (sys.flightExists(a.flightno));
    int t = rnd(1, 10);
    a.flighttype = t <= 2 ? "Heavy" : (t <= 6 ? "Medium" : "Light");        // 20% / 40% / 40%
    a.operationtype = rnd(0, 1) ? "Landing" : "Takeoff";
    a.fuellevel = a.operationtype == "Landing" ? rnd(8, 90) : rnd(50, 100);
    a.emergencystatus = rnd(1, 100) <= 6;
    a.connectingpassengers = rnd(0, a.flighttype == "Heavy" ? 250 : (a.flighttype == "Medium" ? 120 : 30));
    a.runwayrequirements = defaultRunwayReq(a.flighttype);
    a.scheduledtime = nowCeil() + rnd(0, 45);
    return a;
}

static void addAircraftInteractive(AirportSystem& sys) {
    Aircraft a;
    a.flightno = readFlightNo("Flight number (e.g. AI204): ", sys, false);
    int t = readInt("Type  1) Heavy  2) Medium  3) Light : ", 1, 3);
    a.flighttype = t == 1 ? "Heavy" : (t == 2 ? "Medium" : "Light");
    int o = readInt("Operation  1) Landing  2) Takeoff : ", 1, 2);
    a.operationtype = o == 1 ? "Landing" : "Takeoff";
    a.fuellevel = readInt("Fuel level % (0-100): ", 0, 100);
    a.emergencystatus = readYesNo("Declaring an emergency?");
    a.connectingpassengers = readInt("Connecting passengers (0-1000): ", 0, 1000);
    int def = defaultRunwayReq(a.flighttype);
    a.runwayrequirements = readInt("Min runway length needed in m [Enter = " + to_string(def) + "]: ", 500, 6000, true, def);
    int mins = readInt("Scheduled time: minutes from now (-120..720) [Enter = 10]: ", -120, 720, true, 10);
    a.scheduledtime = nowCeil() + mins;
    sys.addAircraft(a);
    cout << "Added " << a.flightno << " to the arrival queue (priority " << fixed << setprecision(1)
         << sys.incoming.at(sys.incoming.size() - 1).priorityscore << ").\n";
}

static void printMenu() {
    cout << "\n" << clr(C_BOLD) << "=========== AIRPORT RUNWAY SCHEDULING ===========" << rst() << "\n"
         << " 1. Add Aircraft                    2. View Waiting Aircraft\n"
         << " 3. View Runway Status              4. Generate Near-Optimal Schedule\n"
         << " 5. Simulate Aircraft Arrival       6. Report Emergency\n"
         << " 7. Close Runway                    8. Reopen Runway\n"
         << " 9. Simulate Weather Change        10. View Today's Operations\n"
         << "11. Performance Analysis           12. Exit\n"
         << " -- extras --\n"
         << "13. Advance Simulation Clock       14. Delay a Flight\n"
         << "15. Runway Timeline (Gantt)        16. Export Schedule to CSV\n"
         << "17. Import Aircraft from CSV\n"
         << "Clock: " << fmtTime((int)getCurrentTime()) << "   Weather: " << weatherName[weatherLevel] << "\n";
}
static int g_pass = 0, g_fail = 0;
#define CHECK(cond, msg) do { if (cond) g_pass++; else { g_fail++; cerr << "FAIL: " << msg << "  [" #cond "] line " << __LINE__ << "\n"; } } while (0)

struct Quiet {                                   // silences cout while a test runs
    ostringstream sink; streambuf* old;
    Quiet() { old = cout.rdbuf(sink.rdbuf()); }
    ~Quiet() { cout.rdbuf(old); }
};
static Aircraft mk(const string& id, double score, int sched = 0) {
    Aircraft a; a.flightno = id; a.priorityscore = score; a.scheduledtime = sched; return a;
}
static Aircraft mkFlight(const string& id, const string& type, const string& op, int fuel, bool em, int req) {
    Aircraft a; a.flightno = id; a.flighttype = type; a.operationtype = op; a.fuellevel = fuel;
    a.emergencystatus = em; a.runwayrequirements = req; a.scheduledtime = 0; return a;
}
static bool scheduleSafe(const AirportSystem& sys) {
    for (auto& r : sys.runways) {
        vector<ScheduledOp> v;
        for (auto& op : sys.schedule) if (op.runwayId == r.id) v.push_back(op);
        sort(v.begin(), v.end(), [](const ScheduledOp& a, const ScheduledOp& b) { return a.start < b.start; });
        for (size_t i = 1; i < v.size(); i++) {
            int gap = v[i].start - v[i - 1].start;
            int base = sepBase[typeIndex(v[i - 1].ac.flighttype)][typeIndex(v[i].ac.flighttype)];
            if (gap < v[i].reqGap || gap < base || gap < v[i - 1].dur) return false;
        }
        for (auto& op : v) if (op.ac.runwayrequirements > r.length) return false;   // compatibility
    }
    return true;
}
static void resetClock() { simScale = 0; simOffset = 0; simStart = steady_clock::now(); weatherLevel = 1; weatherFactor = 1.0; }

static int runSelfTests() {
    resetClock();

    { // --- heap: textbook example from the class notes
        IndexedMaxHeap h; Aircraft a;
        double v[] = {90, 80, 85, 40, 30, 70, 60, 55};
        for (int i = 0; i < 8; i++) { h.insert(mk("F" + to_string(i), v[i])); CHECK(h.validate(), "validate after insert"); }
        vector<double> out;
        while (h.extractMax(a)) { out.push_back(a.priorityscore); CHECK(h.validate(), "validate after extract"); }
        vector<double> expect = {90, 85, 80, 70, 60, 55, 40, 30};
        CHECK(out == expect, "extraction order is descending");
        CHECK(!h.extractMax(a), "extract from empty heap returns false");
        CHECK(h.empty() && h.validate(), "empty heap valid");
    }
    { // --- heap: deterministic tie-breaking
        IndexedMaxHeap h; Aircraft a;
        h.insert(mk("B2", 50, 10)); h.insert(mk("A1", 50, 10)); h.insert(mk("C3", 50, 5)); h.insert(mk("D4", 60, 99));
        h.extractMax(a); CHECK(a.flightno == "D4", "highest score first");
        h.extractMax(a); CHECK(a.flightno == "C3", "tie: earlier scheduledtime first");
        h.extractMax(a); CHECK(a.flightno == "A1", "tie: smaller flight number first");
        h.extractMax(a); CHECK(a.flightno == "B2", "last one");
    }
    { // --- heap: updateKey (increase and decrease) keeps heap + position map consistent
        IndexedMaxHeap h; Aircraft a;
        for (int i = 0; i < 6; i++) h.insert(mk("X" + to_string(i), 10.0 * (i + 1)));
        h.updateKey(mk("X0", 99)); CHECK(h.validate(), "validate after increaseKey");
        h.peekMax(a); CHECK(a.flightno == "X0", "increased key reaches the root");
        h.updateKey(mk("X0", 1)); CHECK(h.validate(), "validate after decreaseKey");
        h.peekMax(a); CHECK(a.flightno == "X5", "decreased key sinks");
        CHECK(!h.updateKey(mk("NOPE", 5)), "update of unknown flight fails");
        CHECK(!h.insert(mk("X1", 5)), "duplicate insert rejected");
    }
    { // --- heap: randomised stress test against a simple reference model
        IndexedMaxHeap h; map<string, Aircraft> ref; mt19937 g(12345); int next = 0; bool ok = true;
        for (int step = 0; step < 4000 && ok; step++) {
            int op = (int)(g() % 3);
            if (op == 0 || ref.empty()) {
                Aircraft a = mk("R" + to_string(next++), (double)(g() % 50), (int)(g() % 5));
                h.insert(a); ref[a.flightno] = a;
            } else if (op == 1) {
                Aircraft best = ref.begin()->second;
                for (auto& kv : ref) if (IndexedMaxHeap::higher(kv.second, best)) best = kv.second;
                Aircraft got; h.extractMax(got);
                if (got.flightno != best.flightno) ok = false;
                ref.erase(best.flightno);
            } else {
                auto it = ref.begin(); advance(it, (long)(g() % ref.size()));
                Aircraft a = it->second; a.priorityscore = (double)(g() % 50); a.scheduledtime = (int)(g() % 5);
                h.updateKey(a); ref[a.flightno] = a;
            }
            if (!h.validate() || h.size() != (int)ref.size()) ok = false;
        }
        CHECK(ok, "4000 random insert/extract/update steps match the reference model");
    }
    { // --- runway min-heap order
        RunwayMinHeap h; RunwayEntry e;
        h.push({1, 12, 0}); h.push({2, 8, 0}); h.push({3, 15, 0}); h.push({4, 8, 0});
        h.pop(e); CHECK(e.runwayId == 2, "earliest free first (tie -> lower id)");
        h.pop(e); CHECK(e.runwayId == 4, "second");
        h.pop(e); CHECK(e.runwayId == 1, "third");
        h.pop(e); CHECK(e.runwayId == 3, "fourth");
        CHECK(!h.pop(e), "pop from empty heap");
    }
    { // --- queue FIFO
        AircraftQueue q; Aircraft a;
        for (int i = 0; i < 100; i++) q.enqueue(mk("Q" + to_string(i), 0));
        bool fifo = true;
        for (int i = 0; i < 100; i++) { q.dequeue(a); if (a.flightno != "Q" + to_string(i)) fifo = false; }
        CHECK(fifo && q.empty() && !q.dequeue(a), "queue is FIFO and survives compaction");
    }
    { // --- priority formula
        resetClock();
        Aircraft a = mkFlight("P1", "Medium", "Landing", 50, true, 2000);
        a.scheduledtime = 30; calculatePriority(a);
        CHECK(fabs(a.priorityscore - (40 + 12.5 + 0.15 * 50)) < 1e-6, "E=100,F=50,T=50 => 60");
        Aircraft b = mkFlight("P2", "Medium", "Landing", 90, false, 2000);
        b.scheduledtime = 500; calculatePriority(b);
        CHECK(fabs(b.priorityscore - 2.5) < 1e-6, "no emergency, fuel 90, far schedule => 2.5");
    }
    { // --- scheduling: emergency first, separation respected
        resetClock();
        AirportSystem sys; sys.addRunway(4000);
        sys.addAircraft(mkFlight("N1", "Heavy", "Landing", 60, false, 3000));
        sys.addAircraft(mkFlight("N2", "Light", "Landing", 60, false, 1500));
        sys.addAircraft(mkFlight("E1", "Medium", "Landing", 60, true, 2000));
        { Quiet q; sys.runSchedulingRound(); }
        CHECK(sys.schedule.size() == 3, "all three scheduled");
        int sE = -1, sN1 = -1;
        for (auto& op : sys.schedule) { if (op.ac.flightno == "E1") sE = op.start; if (op.ac.flightno == "N1") sN1 = op.start; }
        CHECK(sE == 0 && sE < sN1, "emergency flight gets the first slot");
        CHECK(scheduleSafe(sys), "separation respected on the single runway");
        CHECK(sys.conflictsResolved == 2, "two aircraft had to be delayed by separation");
    }
    { // --- compatibility, deferral, reopening
        resetClock();
        AirportSystem sys; sys.addRunway(3000); sys.addRunway(2200);
        sys.addAircraft(mkFlight("BIG", "Heavy", "Landing", 40, false, 3500));
        { Quiet q; sys.runSchedulingRound(); }
        CHECK(sys.schedule.empty() && sys.waiting.size() == 1, "too-long requirement is deferred, not scheduled");
        sys.addRunway(4000);
        { Quiet q; sys.runSchedulingRound(); }
        CHECK(sys.schedule.size() == 1 && sys.schedule[0].runwayId == 3, "scheduled once a long runway exists");
    }
    { // --- runway closure / reopening (lazy invalidation) + conservation of aircraft
        resetClock();
        AirportSystem sys; sys.initDefaultRunways();
        for (int i = 0; i < 8; i++)
            sys.addAircraft(mkFlight("M" + to_string(i), "Medium", i % 2 ? "Landing" : "Takeoff", 20 + 7 * i, false, 2000));
        { Quiet q; sys.runSchedulingRound(); }
        CHECK(sys.schedule.size() == 8 && scheduleSafe(sys), "8 scheduled safely");
        { Quiet q; sys.closeRunway(1); }
        bool futureOnR1 = false;
        for (auto& op : sys.schedule) if (op.runwayId == 1 && op.start > 0) futureOnR1 = true;
        CHECK(!futureOnR1, "no future operation left on the closed runway");
        CHECK((int)sys.schedule.size() + sys.waiting.size() == 8, "no aircraft lost or duplicated");
        CHECK(scheduleSafe(sys), "safe after closure re-plan");
        { Quiet q; sys.closeRunway(2); sys.closeRunway(3); }
        CHECK((int)sys.schedule.size() + sys.waiting.size() == 8, "still conserved with all runways closed");
        { Quiet q; sys.reopenRunway(2); }
        CHECK(sys.rw(2).isOpen && scheduleSafe(sys), "reopened runway used again");
        CHECK((int)sys.schedule.size() + sys.waiting.size() == 8, "conserved after reopening");
    }
    { // --- emergency on an already planned flight jumps the queue; weather widens separation
        resetClock();
        AirportSystem sys; sys.addRunway(4000);
        for (int i = 0; i < 4; i++) sys.addAircraft(mkFlight("W" + to_string(i), "Heavy", "Landing", 50, false, 3000));
        { Quiet q; sys.runSchedulingRound(); }
        int before = -1;
        for (auto& op : sys.schedule) if (op.ac.flightno == "W3") before = op.start;
        { Quiet q; sys.reportEmergency("W3"); }
        int after = -1;
        for (auto& op : sys.schedule) if (op.ac.flightno == "W3") after = op.start;
        CHECK(after < before, "emergency moved earlier in the plan");
        CHECK(scheduleSafe(sys), "safe after emergency re-plan");
        { Quiet q; sys.setWeather(4); }
        CHECK(sepMin(0, 0) == 6 && opDuration() == 2, "severe weather doubles separation and duration");
        CHECK(scheduleSafe(sys) && (int)sys.schedule.size() + sys.waiting.size() == 4, "safe + conserved after weather");
    }
    { // --- empty system
        resetClock();
        AirportSystem sys; sys.initDefaultRunways();
        Quiet q;
        CHECK(sys.runSchedulingRound() == 0, "empty system schedules nothing");
        sys.printWaiting(); sys.printOperations(); sys.printMetrics(); sys.printTimeline(); sys.printRunways();
        CHECK(true, "views on an empty system do not crash");
    }
    resetClock();
    cout << "Self tests: " << g_pass << " passed, " << g_fail << " failed.\n";
    return g_fail == 0 ? 0 : 1;
}

int main(int argc, char** argv) {
    bool testMode = false;
    for (int i = 1; i < argc; i++) {
        string s = argv[i];
        if (s == "--test") testMode = true;
        else if (s == "--nocolor") useColor = false;
        else if (s == "--scale" && i + 1 < argc) { try { simScale = max(0.0, stod(argv[++i])); } catch (...) { cerr << "bad --scale\n"; return 1; } }
        else if (s == "--seed" && i + 1 < argc) { try { rng.seed((unsigned)stoul(argv[++i])); } catch (...) { cerr << "bad --seed\n"; return 1; } }
        else if (s == "--help") {
            cout << "Usage: runway [--scale X] [--seed N] [--nocolor] [--test]\n"
                    "  --scale X   simulated minutes per real second (default 3, 0 = frozen, use menu 13)\n";
            return 0;
        }
    }
    cout << fixed << setprecision(1);
    simStart = steady_clock::now();                                // captured ONCE
    if (testMode) { useColor = false; return runSelfTests(); }

    logFile.open("runway_log.txt", ios::app);
    logEvent("---- session started ----");

    AirportSystem sys;
    sys.initDefaultRunways();
    cout << clr(C_BOLD) << "Intelligent Airport Runway Scheduling System" << rst() << "\n"
         << "Simulation clock: " << simScale << " sim-minutes per real second"
         << (simScale == 0 ? " (frozen - use option 13 to advance)" : "") << ".\n";

    while (true) {
        printMenu();
        int choice = readInt("Choice: ", 1, 17);
        switch (choice) {
        case 1: addAircraftInteractive(sys); break;
        case 2: sys.printWaiting(); break;
        case 3: sys.printRunways(); break;
        case 4: sys.runSchedulingRound(); break;
        case 5: {
            int n = readInt("How many aircraft arrive? (1-20) [Enter = 3]: ", 1, 20, true, 3);
            for (int i = 0; i < n; i++) {
                Aircraft a = makeRandomAircraft(sys);
                sys.addAircraft(a);
                cout << "  arrived: " << a.flightno << " " << a.flighttype << " " << a.operationtype
                     << (a.emergencystatus ? "  (EMERGENCY)" : "") << "\n";
            }
            cout << "Use option 4 to schedule them.\n";
            break;
        }
        case 6: sys.reportEmergency(readFlightNo("Flight number declaring emergency: ", sys, true)); break;
        case 7: sys.printRunways(); sys.closeRunway(readInt("Runway number to close: ", 1, (int)sys.runways.size())); break;
        case 8: sys.printRunways(); sys.reopenRunway(readInt("Runway number to reopen: ", 1, (int)sys.runways.size())); break;
        case 9: {
            cout << "Weather: 1) Clear  2) Light rain (x1.25)  3) Thunderstorm (x1.5)  4) Severe storm (x2.0)\n";
            sys.setWeather(readInt("Choose weather: ", 1, 4));
            break;
        }
        case 10: sys.printOperations(); break;
        case 11: sys.printMetrics(); break;
        case 12: cout << "Goodbye. Decision log saved in runway_log.txt\n"; logEvent("---- session ended ----"); return 0;
        case 13: {
            int m = readInt("Advance the simulation clock by how many minutes (1-600)? ", 1, 600);
            simOffset += m;
            cout << "Clock is now " << fmtTime((int)getCurrentTime()) << ".\n";
            logEvent("CLOCK advanced by " + to_string(m) + " min");
            break;
        }
        case 14: {
            string id = readFlightNo("Flight number to delay: ", sys, true);
            sys.delayFlight(id, readInt("Delay in minutes (1-300): ", 1, 300));
            break;
        }
        case 15: sys.printTimeline(); break;
        case 16: {
            cout << "File name [Enter = schedule_export.csv]: ";
            string fn = readLine(); if (fn.empty()) fn = "schedule_export.csv";
            cout << (sys.exportSchedule(fn) ? "Schedule exported to " + fn : "Could not write " + fn) << "\n";
            break;
        }
        case 17: {
            cout << "CSV file [Enter = sample_aircraft.csv]: ";
            string fn = readLine(); if (fn.empty()) fn = "sample_aircraft.csv";
            if (sys.importAircraft(fn) < 0) cout << "Could not open " << fn << ".\n";
            else cout << "Use option 4 to schedule them.\n";
            break;
        }
        }
    }
}
