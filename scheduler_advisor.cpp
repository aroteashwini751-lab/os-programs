// CPU Scheduling Algorithm Decision Simulator
// Given process characteristics, it (1) analyses the workload, (2) simulates the
// candidate algorithms, (3) scores them with explainable rules + simulation results,
// and (4) recommends the most suitable algorithm.
//
// Build:  g++ -std=c++17 -O2 scheduler_advisor.cpp -o advisor
// Run:    ./advisor            (then type input, or:  ./advisor < input.txt)
//
// Input format:
//   n
//   arrival burst priority deadline      (n lines; lower priority number = higher priority;
//                                         deadline = relative to arrival, 0 = none)
//   preemptionAllowed (1/0)
//   burstTimesKnown   (1/0)              (can burst times be predicted/estimated?)
//   systemType        (1=batch, 2=interactive/time-sharing, 3=real-time)
//   goal              (1=min avg waiting, 2=fast response, 3=fairness, 4=simplicity)

#include <bits/stdc++.h>
using namespace std;

struct Process { int id, at, bt, pr, dl; };

enum Algo { FCFS, SJF, SRTF, PRIO_NP, PRIO_P, RR, EDF, ALGO_COUNT };
const char* algoName[] = {
    "FCFS", "SJF (non-preemptive)", "SRTF (preemptive SJF)",
    "Priority (non-preemptive)", "Priority (preemptive)", "Round Robin", "EDF (Earliest Deadline First)"};

struct Result {
    Algo a;
    bool applicable = true;
    string naReason;
    double wt = 0, tat = 0, rt = 0, maxWt = 0;
    int cs = 0, missed = 0;
    vector<int> gantt;  // process id per time unit, -1 = idle
    double score = 0;
    vector<string> why;
};

struct Env { bool preempt, burstKnown; int sysType, goal; };

struct Stats {
    int n;
    double meanBt, sdBt, cv;
    int minBt, maxBt, q80;
    bool simultaneous, hasPriority, hasDeadlines;
};

// ---------------------------------------------------------------- simulation
Result simulate(const vector<Process>& ps, Algo a, int q) {
    int n = ps.size();
    vector<int> rem(n), first(n, -1), ct(n, 0);
    for (int i = 0; i < n; i++) rem[i] = ps[i].bt;
    Result r; r.a = a;
    int t = 0, done = 0;

    if (a == RR) {
        vector<int> order(n);
        iota(order.begin(), order.end(), 0);
        stable_sort(order.begin(), order.end(), [&](int x, int y) { return ps[x].at < ps[y].at; });
        size_t nxt = 0;
        queue<int> rq;
        auto admit = [&](int upto) {
            while (nxt < order.size() && ps[order[nxt]].at <= upto) rq.push(order[nxt++]);
        };
        while (done < n) {
            admit(t);
            if (rq.empty()) { r.gantt.push_back(-1); t++; continue; }
            int p = rq.front(); rq.pop();
            if (first[p] < 0) first[p] = t;
            int run = min(q, rem[p]);
            for (int k = 0; k < run; k++) { r.gantt.push_back(ps[p].id); t++; admit(t); }
            rem[p] -= run;
            if (rem[p] > 0) rq.push(p); else { ct[p] = t; done++; }
        }
    } else {
        bool preempt = (a == SRTF || a == PRIO_P || a == EDF);
        int cur = -1;
        auto key = [&](int i) {
            long k = 0;
            switch (a) {
                case SJF: case SRTF: k = rem[i]; break;
                case PRIO_NP: case PRIO_P: k = ps[i].pr; break;
                case EDF: k = ps[i].dl > 0 ? ps[i].at + ps[i].dl : LONG_MAX / 2; break;
                default: k = 0;  // FCFS: ordered by arrival below
            }
            return make_tuple(k, i == cur ? 0 : 1, ps[i].at, ps[i].id);
        };
        while (done < n) {
            if (cur == -1 || preempt) {
                int best = -1;
                for (int i = 0; i < n; i++)
                    if (ps[i].at <= t && rem[i] > 0 && (best < 0 || key(i) < key(best))) best = i;
                cur = best;
            }
            if (cur == -1) { r.gantt.push_back(-1); t++; continue; }
            if (first[cur] < 0) first[cur] = t;
            r.gantt.push_back(ps[cur].id);
            t++; rem[cur]--;
            if (rem[cur] == 0) { ct[cur] = t; done++; cur = -1; }
        }
    }

    for (int i = 0; i < n; i++) {
        double tat = ct[i] - ps[i].at, wt = tat - ps[i].bt, rt = first[i] - ps[i].at;
        r.tat += tat; r.wt += wt; r.rt += rt;
        r.maxWt = max(r.maxWt, wt);
        if (ps[i].dl > 0 && ct[i] > ps[i].at + ps[i].dl) r.missed++;
    }
    r.tat /= n; r.wt /= n; r.rt /= n;
    int last = -1;
    for (int p : r.gantt) {
        if (p == -1) continue;
        if (last != -1 && p != last) r.cs++;
        last = p;
    }
    return r;
}

// ---------------------------------------------------------------- analysis
Stats analyse(const vector<Process>& ps) {
    Stats s; s.n = ps.size();
    vector<int> b;
    for (auto& p : ps) b.push_back(p.bt);
    sort(b.begin(), b.end());
    s.minBt = b.front(); s.maxBt = b.back();
    s.meanBt = accumulate(b.begin(), b.end(), 0.0) / s.n;
    double var = 0;
    for (int x : b) var += (x - s.meanBt) * (x - s.meanBt);
    s.sdBt = sqrt(var / s.n);
    s.cv = s.meanBt > 0 ? s.sdBt / s.meanBt : 0;
    s.q80 = max(1, b[(int)ceil(0.8 * s.n) - 1]);
    s.simultaneous = all_of(ps.begin(), ps.end(), [&](const Process& p) { return p.at == ps[0].at; });
    s.hasPriority = any_of(ps.begin(), ps.end(), [&](const Process& p) { return p.pr != ps[0].pr; });
    s.hasDeadlines = any_of(ps.begin(), ps.end(), [](const Process& p) { return p.dl > 0; });
    return s;
}

// ---------------------------------------------------------------- scoring
void scoreAll(vector<Result>& R, const Stats& s, const Env& e) {
    auto add = [&](Algo a, double pts, const string& why) {
        if (!R[a].applicable) return;
        R[a].score += pts;
        R[a].why.push_back(string(pts >= 0 ? "+" : "") + to_string((int)pts) + "  " + why);
    };

    // applicability
    auto na = [&](Algo a, const string& reason) { R[a].applicable = false; R[a].naReason = reason; };
    if (!e.burstKnown) { na(SJF, "needs known/estimated burst times"); na(SRTF, "needs known/estimated burst times"); }
    if (!e.preempt) {
        for (Algo a : {SRTF, PRIO_P, RR, EDF}) na(a, "needs preemption");
    }
    if (!s.hasPriority) { na(PRIO_NP, "all priorities are equal"); na(PRIO_P, "all priorities are equal"); }
    if (!s.hasDeadlines) na(EDF, "no deadlines given");

    // system type
    if (e.sysType == 3) {
        add(EDF, 60, "real-time system: EDF meets deadlines whenever a feasible schedule exists");
        add(PRIO_P, 15, "real-time system: preemptive priorities give quick reaction to urgent tasks");
        add(FCFS, -25, "real-time system: no regard for urgency");
    } else if (e.sysType == 2) {
        add(RR, 30, "interactive system: time slicing bounds response time");
        add(SRTF, 10, "interactive system: short jobs finish quickly");
        add(FCFS, -20, "interactive system: long jobs block everyone behind them");
        add(SJF, -10, "interactive system: non-preemptive, poor responsiveness");
        add(PRIO_NP, -10, "interactive system: non-preemptive, poor responsiveness");
    } else {
        add(SJF, 20, "batch system: shortest-first minimises average waiting time");
        add(SRTF, 10, "batch system: optimal average waiting time (preemptive)");
        add(FCFS, 10, "batch system: simple, no switching overhead");
        add(RR, -10, "batch system: context-switch overhead gives no benefit");
    }

    // burst variability
    if (s.cv > 0.6) {
        add(FCFS, -15, "highly variable burst times -> convoy effect risk");
        add(SJF, 15, "highly variable bursts -> big gain from running short jobs first");
        add(SRTF, 15, "highly variable bursts -> big gain from running short jobs first");
    } else if (s.cv <= 0.25) {
        add(FCFS, 15, "similar burst times -> FCFS is nearly as good as anything");
        add(SJF, -5, "similar burst times -> little gain from sorting by length");
        add(SRTF, -5, "similar burst times -> little gain from sorting by length");
        add(RR, -5, "similar burst times -> time slicing only adds overhead");
    }

    // priorities
    if (s.hasPriority) {
        add(PRIO_NP, 15, "processes carry meaningful priorities");
        add(PRIO_P, 15, "processes carry meaningful priorities");
    }

    // arrivals
    if (!s.simultaneous) add(SRTF, 5, "staggered arrivals: preemption can reorder work as jobs arrive");

    // user goal
    switch (e.goal) {
        case 1: add(SJF, 10, "goal: minimum average waiting time"); add(SRTF, 15, "goal: minimum average waiting time"); break;
        case 2: add(RR, 15, "goal: fast response"); add(SRTF, 10, "goal: fast response"); break;
        case 3:
            add(RR, 20, "goal: fairness (every process gets regular CPU turns)");
            add(FCFS, 10, "goal: fairness (strict arrival order)");
            add(SJF, -10, "goal: fairness (long jobs may starve)");
            add(SRTF, -10, "goal: fairness (long jobs may starve)");
            add(PRIO_NP, -10, "goal: fairness (low priority may starve)");
            add(PRIO_P, -10, "goal: fairness (low priority may starve)");
            break;
        case 4: add(FCFS, 25, "goal: simplicity"); break;
    }

    // evidence from the simulation
    if (s.hasDeadlines)
        for (auto& r : R) if (r.applicable && r.missed > 0)
            add(r.a, -15.0 * r.missed, to_string(r.missed) + " deadline(s) missed in simulation");

    if (e.goal != 4) {
        auto metric = [&](const Result& r) { return e.goal == 1 ? r.wt : e.goal == 2 ? r.rt : r.maxWt; };
        const char* mname = e.goal == 1 ? "avg waiting time" : e.goal == 2 ? "avg response time" : "worst-case waiting time";
        vector<int> idx;
        for (int i = 0; i < ALGO_COUNT; i++) if (R[i].applicable) idx.push_back(i);
        stable_sort(idx.begin(), idx.end(), [&](int x, int y) { return metric(R[x]) < metric(R[y]); });
        if (idx.size() > 0) add((Algo)idx[0], 20, string("best ") + mname + " in simulation");
        if (idx.size() > 1) add((Algo)idx[1], 10, string("2nd best ") + mname + " in simulation");
    }
}

// ---------------------------------------------------------------- output
void printGantt(const vector<int>& g) {
    string bar = "|", ticks = "0";
    int start = 0;
    for (size_t i = 1; i <= g.size(); i++) {
        if (i == g.size() || g[i] != g[start]) {
            string lab = g[start] == -1 ? "idle" : "P" + to_string(g[start]);
            int w = max<int>(lab.size() + 2, 4);
            int padL = (w - lab.size()) / 2, padR = w - lab.size() - padL;
            bar += string(padL, ' ') + lab + string(padR, ' ') + "|";
            string t = to_string(i);
            ticks += string(w + 1 - t.size(), ' ') + t;
            start = i;
        }
    }
    cout << bar << "\n" << ticks << "\n";
}

int main() {
    int n;
    cout << "Number of processes: ";
    if (!(cin >> n) || n <= 0) { cerr << "Invalid process count.\n"; return 1; }
    vector<Process> ps(n);
    cout << "Enter for each process: arrival burst priority deadline(0=none)\n";
    for (int i = 0; i < n; i++) {
        ps[i].id = i + 1;
        if (!(cin >> ps[i].at >> ps[i].bt >> ps[i].pr >> ps[i].dl) || ps[i].at < 0 || ps[i].bt <= 0 || ps[i].dl < 0) {
            cerr << "Invalid data for process " << i + 1 << " (arrival>=0, burst>0, deadline>=0).\n";
            return 1;
        }
    }
    Env e; int pre, known;
    cout << "Preemption allowed? (1/0): ";            cin >> pre;
    cout << "Burst times known/estimable? (1/0): ";   cin >> known;
    cout << "System type (1=batch 2=interactive 3=real-time): "; cin >> e.sysType;
    cout << "Goal (1=min avg wait 2=fast response 3=fairness 4=simplicity): "; cin >> e.goal;
    e.preempt = pre; e.burstKnown = known;
    if (e.sysType < 1 || e.sysType > 3 || e.goal < 1 || e.goal > 4) { cerr << "Invalid system type or goal.\n"; return 1; }

    Stats s = analyse(ps);
    int quantum = s.q80;

    cout << fixed << setprecision(2);
    cout << "\n=== Workload characteristics ===\n"
         << "Processes: " << s.n << " | burst min/mean/max: " << s.minBt << "/" << s.meanBt << "/" << s.maxBt << "\n"
         << "Burst variability (CV): " << s.cv << (s.cv > 0.6 ? "  [high]" : s.cv <= 0.25 ? "  [low]" : "  [moderate]") << "\n"
         << "Arrivals: " << (s.simultaneous ? "all together" : "staggered") << " | priorities: "
         << (s.hasPriority ? "meaningful" : "not used") << " | deadlines: " << (s.hasDeadlines ? "yes" : "none") << "\n"
         << "Suggested RR quantum (covers ~80% of bursts): " << quantum << "\n";

    vector<Result> R(ALGO_COUNT);
    for (int a = 0; a < ALGO_COUNT; a++) R[a].a = (Algo)a;
    scoreAll(R, s, e);  // first pass only to set applicability (scores reset below)

    vector<Result> sims(ALGO_COUNT);
    for (int a = 0; a < ALGO_COUNT; a++) {
        if (!R[a].applicable) { sims[a].a = (Algo)a; sims[a].applicable = false; sims[a].naReason = R[a].naReason; continue; }
        sims[a] = simulate(ps, (Algo)a, quantum);
    }
    scoreAll(sims, s, e);  // final scoring with simulation evidence

    cout << "\n=== Simulation results ===\n";
    cout << left << setw(32) << "Algorithm" << right << setw(9) << "AvgWT" << setw(9) << "AvgTAT"
         << setw(9) << "AvgRT" << setw(9) << "MaxWT" << setw(8) << "Switch";
    if (s.hasDeadlines) cout << setw(8) << "Missed";
    cout << setw(8) << "Score" << "\n" << string(s.hasDeadlines ? 100 : 92, '-') << "\n";
    for (auto& r : sims) {
        cout << left << setw(32) << algoName[r.a];
        if (!r.applicable) { cout << "not applicable (" << r.naReason << ")\n"; continue; }
        cout << right << setw(9) << r.wt << setw(9) << r.tat << setw(9) << r.rt << setw(9) << r.maxWt << setw(8) << r.cs;
        if (s.hasDeadlines) cout << setw(8) << r.missed;
        cout << setw(8) << r.score << "\n";
    }

    vector<int> order;
    for (int a = 0; a < ALGO_COUNT; a++) if (sims[a].applicable) order.push_back(a);
    if (order.empty()) { cout << "\nNo applicable algorithm for these constraints.\n"; return 0; }
    stable_sort(order.begin(), order.end(), [&](int x, int y) { return sims[x].score > sims[y].score; });
    const Result& best = sims[order[0]];

    cout << "\n=== RECOMMENDATION: " << algoName[best.a];
    if (best.a == RR) cout << " (quantum = " << quantum << ")";
    cout << " ===\nWhy:\n";
    for (auto& w : best.why) cout << "  " << w << "\n";
    if (order.size() > 1) {
        const Result& second = sims[order[1]];
        cout << "Runner-up: " << algoName[second.a] << " (score " << second.score << ", margin "
             << best.score - second.score << ")\n";
    }
    cout << "Watch out: ";
    switch (best.a) {
        case SJF: case SRTF: cout << "long jobs can starve; burst estimates must be reasonably accurate.\n"; break;
        case PRIO_NP: case PRIO_P: cout << "low-priority starvation; add aging to raise priority over time.\n"; break;
        case RR: cout << "quantum too small -> switching overhead; too large -> behaves like FCFS.\n"; break;
        case EDF: cout << "overload causes cascading deadline misses; needs reliable deadline/burst data.\n"; break;
        case FCFS: cout << "convoy effect if a long job arrives early.\n"; break;
        default: cout << "\n"; break;
    }
    cout << "\nGantt chart (" << algoName[best.a] << "):\n";
    printGantt(best.gantt);
    return 0;
}
