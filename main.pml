/*
 *  This file is part of traffic lights model development and verification.
 *
 *  Copyright (C) 2010  Vladimir Rutsky <altsysrq@gmail.com>
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

  /* Variant 9-13:
   * SN, WE, NE, ES.
   */
  /*
   *               N
   *           2
   *           |       ^
   *           |       |
   *           |     --2-------3
   *            \   /  |
   *  W           4    |          E
   *            /   \  |
   *           /     --1------>
   *           |       |
   *    1 -----3-------0------>
   *           |       |
   *           v       |
   *                   0
   *               S
   *
   */

#define NE 0
#define EW 1
#define SW 2
#define ES 3
#define SN 4

/* Number of traffic lights */
#define N_TRAFFIC_LIGHTS 5

/* Number of intersections */
#define N_INTERSECTIONS  6

/* Car object */
mtype = { CAR };

/* Cars waiting sign for each traffic light */
chan carsWaiting[N_TRAFFIC_LIGHTS] = [1] of { mtype };

proctype LineTrafficGenerator( byte initTlId )
{
  byte tlId;
  
  tlId = initTlId;
  
  do
  :: carsWaiting[tlId] ! CAR;
  od
}

/* Manager messages */
mtype = { LOCK, INT, RELEASE };

/* Intersections lock/release requests queue.
 * Message contains requestee traffic light identifier.
 */
chan intersectionLockRequests[N_INTERSECTIONS] = 
  [N_TRAFFIC_LIGHTS] of { mtype, byte };
chan intersectionLockGranted[N_TRAFFIC_LIGHTS] = 
  [0] of { mtype };
chan intersectionReleaseRequests[N_INTERSECTIONS] = 
  [0] of { mtype };

/* Macro for obtaining intersection resource */
#define lockIntersection( intId, tlId )   \
  intersectionLockRequests[intId] ! LOCK(tlId); \
  intersectionLockGranted[tlId] ? INT

/* Macro for releasing intersection resource */
#define unlockIntersection( intId ) \
  intersectionReleaseRequests[intId] ! RELEASE

/* Intersection resource manager */
proctype Intersection( byte initIntId )
{
  byte intId, tlId;

  intId = initIntId;

endInt:
  do
  :: intersectionLockRequests[intId] ? LOCK(tlId) ->
    /* Handle request */
    intersectionLockGranted[tlId] ! INT;

    /* Wait for release */
  progressGiveIntersection:
    intersectionReleaseRequests[intId] ? RELEASE;
  od;
}

/* Traffic lights states */
mtype = { RED, GREEN };

/* Traffic light state */
mtype tlColor[N_TRAFFIC_LIGHTS];

/* Main traffic light process */
proctype TrafficLight( byte initTlId )
{
  byte tlId;
  
  tlId = initTlId;

  assert(tlColor[tlId] == RED);

endTL:
  do
  :: carsWaiting[tlId] ? [CAR] ->
    /* Cars in queue */
  
    /* Lock dependent intersections */
    if
    :: tlId == NE ->
      lockIntersection(0, tlId);
      lockIntersection(3, tlId);
      lockIntersection(5, tlId);
    :: tlId == EW ->
      lockIntersection(2, tlId);
      lockIntersection(3, tlId);
    :: tlId == SW ->
      lockIntersection(4, tlId);
    :: tlId == ES ->
      lockIntersection(1, tlId);
      lockIntersection(4, tlId);
      lockIntersection(5, tlId);
    :: tlId == SN ->
      lockIntersection(0, tlId);
      lockIntersection(1, tlId);
      lockIntersection(2, tlId);
    fi;
    
      tlColor[tlId] = GREEN;
      carsWaiting[tlId] ? CAR;
      tlColor[tlId] = RED;
    
    /* Release dependent intersections */
    if
    :: tlId == NE ->
      unlockIntersection(5);
      unlockIntersection(3);
      unlockIntersection(0);
    :: tlId == EW ->
      unlockIntersection(3);
      unlockIntersection(2);
    :: tlId == SW ->
      unlockIntersection(4);
    :: tlId == ES ->
      unlockIntersection(5);
      unlockIntersection(4);
      unlockIntersection(1);
    :: tlId == SN ->
      unlockIntersection(2);
      unlockIntersection(1);
      unlockIntersection(0);
    fi;
  od;
}

/* The main model function */
init
{
  byte tlId, intId;
  
  /* Reset traffic lights colors */
  tlId = 0;
  do
  :: tlId < N_TRAFFIC_LIGHTS ->
    tlColor[tlId] = RED;
    tlId++;
  :: else ->
    break;
  od;
  
  atomic
  {
    /* Start intersection managers processes */
    intId = 0;
    do
    :: intId < N_INTERSECTIONS ->
      run Intersection(intId);
      intId++;
    :: else ->
      break;
    od;
  
    /* Start traffic lights processes */
    tlId = 0;
    do
    :: tlId < N_TRAFFIC_LIGHTS ->
      run TrafficLight(tlId);
      tlId++;
    :: else ->
      break;
    od;
  
    /* Start cars generator process */
    /*run CarsGenerator();*/
    tlId = 0;
    do
    :: tlId < N_TRAFFIC_LIGHTS ->
      run LineTrafficGenerator(tlId);
      tlId++;
    :: else ->
      break;
    od;
  }
}

#define ltl_safety \
[] !(tlColor[0] == GREEN && tlColor[1] == GREEN) && \
[] !(tlColor[0] == GREEN && tlColor[3] == GREEN) && \
[] !(tlColor[0] == GREEN && tlColor[4] == GREEN) && \
[] !(tlColor[1] == GREEN && tlColor[4] == GREEN) && \
[] !(tlColor[2] == GREEN && tlColor[3] == GREEN) && \
[] !(tlColor[3] == GREEN && tlColor[4] == GREEN)

#define ltl_liveness \
[] ((len(carsWaiting[0]) > 0) -> <> (tlColor[0] == GREEN)) && \
[] ((len(carsWaiting[1]) > 0) -> <> (tlColor[1] == GREEN)) && \
[] ((len(carsWaiting[2]) > 0) -> <> (tlColor[2] == GREEN)) && \
[] ((len(carsWaiting[3]) > 0) -> <> (tlColor[3] == GREEN)) && \
[] ((len(carsWaiting[4]) > 0) -> <> (tlColor[4] == GREEN))

#define ltl_fairness \
[] <> !((tlColor[0] == GREEN) && (len(carsWaiting[0]) > 0)) && \
[] <> !((tlColor[1] == GREEN) && (len(carsWaiting[1]) > 0)) && \
[] <> !((tlColor[2] == GREEN) && (len(carsWaiting[2]) > 0)) && \
[] <> !((tlColor[3] == GREEN) && (len(carsWaiting[3]) > 0)) && \
[] <> !((tlColor[4] == GREEN) && (len(carsWaiting[4]) > 0))

ltl safety{ltl_safety};
ltl liveness{ltl_liveness};
ltl fairness{ltl_fairness};
