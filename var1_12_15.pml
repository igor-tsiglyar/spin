#define NS	0
#define NE	1
#define WN	2
#define EW	3
#define ES	4
#define SW	5

#define LIGHTS_COUNT	6

ltl safety {
	[] !(g_green[NS] && g_green[EW]) &&
	[] !(g_green[NE] && g_green[EW]) &&
	[] !(g_green[WN] && g_green[EW]) &&
	[] !(g_green[NE] && g_green[WN]) &&
	[] !(g_green[NS] && g_green[SW]) &&
	[] !(g_green[WN] && g_green[SW]) &&
	[] !(g_green[NE] && g_green[ES]) &&
	[] !(g_green[NS] && g_green[WN]) &&
	[] !(g_green[ES] && g_green[SW])
};

ltl liveness {
	[](((g_enter[NS] ? [CAR]) && !g_green[NS]) -> <>(g_green[NS])) &&
	[](((g_enter[NE] ? [CAR]) && !g_green[NE]) -> <>(g_green[NE])) &&
	[](((g_enter[WN] ? [CAR]) && !g_green[WN]) -> <>(g_green[WN])) &&
	[](((g_enter[EW] ? [CAR]) && !g_green[EW]) -> <>(g_green[EW])) &&
	[](((g_enter[ES] ? [CAR]) && !g_green[ES]) -> <>(g_green[ES])) &&
	[](((g_enter[SW] ? [CAR]) && !g_green[SW]) -> <>(g_green[SW]))
};

ltl fairness {
    []<> !((g_enter[NS] ? [CAR]) && g_green[NS]) &&
    []<> !((g_enter[NE] ? [CAR]) && g_green[NE]) &&
    []<> !((g_enter[WN] ? [CAR]) && g_green[WN]) &&
    []<> !((g_enter[EW] ? [CAR]) && g_green[EW]) &&
    []<> !((g_enter[ES] ? [CAR]) && g_green[ES]) &&
    []<> !((g_enter[SW] ? [CAR]) && g_green[SW])
};
			
mtype = {CAR};
chan g_enter[LIGHTS_COUNT] = [1] of {mtype};
bit g_green[LIGHTS_COUNT];

mtype = {GRANTED};
chan g_ack[LIGHTS_COUNT] = [0] of {mtype};
chan g_queue = [LIGHTS_COUNT] of {byte};
byte g_locked[LIGHTS_COUNT];

proctype intersection_ctrl()
{
	byte id;
end:do
	:: g_queue ? id ->
		(g_locked[id] == 0);
		if
		:: id == ES -> 
			g_locked[NE]++; 
			g_locked[SW]++;
		:: id == NS -> 
			g_locked[EW]++; 
			g_locked[SW]++; 
			g_locked[WN]++;
		:: id == NE -> 
			g_locked[EW]++; 
			g_locked[WN]++; 
			g_locked[ES]++;
		:: id == EW -> 
			g_locked[WN]++; 
			g_locked[NE]++; 
			g_locked[NS]++;
		:: id == SW -> 
			g_locked[ES]++; 
			g_locked[WN]++; 
			g_locked[NS]++;
		:: id == WN -> 
			g_locked[NS]++; 
			g_locked[SW]++; 
			g_locked[NE]++; 
			g_locked[EW]++;
		fi
		g_ack[id] ! GRANTED;
	od
}
 
proctype traffic_light(byte id)
{
end:do
	:: g_enter[id] ? [CAR] ->
		g_queue! id;
		g_ack[id] ? GRANTED;
		g_green[id] = true;
		g_enter[id] ? CAR;
		g_green[id] = false;
		d_step { 
			if
			:: id == ES -> 
				g_locked[NE]--; 
				g_locked[SW]--;
			:: id == NS -> 
				g_locked[EW]--; 
				g_locked[SW]--; 
				g_locked[WN]--;
			:: id == NE -> 
				g_locked[EW]--; 
				g_locked[WN]--; 
				g_locked[ES]--;
			:: id == EW -> 
				g_locked[WN]--; 
				g_locked[NE]--; 
				g_locked[NS]--;
			:: id == SW -> 
				g_locked[ES]--; 
				g_locked[WN]--; 
				g_locked[NS]--;
			:: id == WN -> 
				g_locked[NS]--; 
				g_locked[SW]--; 
				g_locked[NE]--; 
				g_locked[EW]--;
			fi 
		}
	od
}

proctype flow(byte id)
{
end:do
	:: g_enter[id] ! CAR
	od
}
 
init {
	atomic {
		run intersection_ctrl();
		run traffic_light(0);
		run traffic_light(1);
		run traffic_light(2);
		run traffic_light(3);
		run traffic_light(4);
		run traffic_light(5);
		run flow(0);
		run flow(1);
		run flow(2);
		run flow(3);
		run flow(4);
		run flow(5);
	}
}