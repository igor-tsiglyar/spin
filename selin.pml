mtype = { red, green };

mtype lightNE = red;
mtype lightEW = red;
mtype lightSW = red;
mtype lightES = red;
mtype lightSN = red;

bool detectorNE = false;
bool detectorEW = false;
bool detectorSW = false;
bool detectorES = false;
bool detectorSN = false;

chan SN_NE = [1] of {bool};
chan SN_ES = [1] of {bool};
chan SN_EW = [1] of {bool};
chan EW_NE = [1] of {bool};
chan ES_SW = [1] of {bool};
chan ES_NE = [1] of {bool};

init {
  atomic {
    SN_NE ! true;
    SN_ES ! true;
    SN_EW ! true;
    EW_NE ! true;
    ES_SW ! true;
    ES_NE ! true;
  }
}

active proctype GeneratorNE() {
  do
    :: (!detectorNE) ->
      detectorNE = true;
    :: lightNE == green ->
      detectorNE = false;
  od;
}

active proctype GeneratorEW() {
  do
    :: (!detectorEW) ->
      detectorEW = true;
    :: lightEW == green ->
      detectorEW = false;
  od;
}

active proctype GeneratorSW() {
  do
    :: (!detectorSW) ->
      detectorSW = true;
    :: lightSW == green ->
      detectorSW = false;
  od;
}

active proctype GeneratorES() {
  do
    :: (!detectorES) ->
      detectorES = true;
    :: lightES == green ->
      detectorES = false;
  od;
}

active proctype GeneratorSN() {
  do
    :: (!detectorSN) ->
      detectorSN = true;
    :: lightSN == green ->
      detectorSN = false;
  od;
}


active proctype ControllerNE() {
  do
    :: detectorNE ->
    SN_NE ? true;
    EW_NE ? true;
    ES_NE ? true;
    lightNE = green;
    lightNE = red;
    SN_NE ! true;
    EW_NE ! true;
    ES_NE ! true;
  od;
}

active proctype ControllerEW() {
  do
    :: detectorEW ->
	  SN_EW ? true;
	  EW_NE ? true;
	  lightEW = green;
	  lightEW = red;
	  SN_EW ! true;
	  EW_NE ! true;
  od;
}

active proctype ControllerSW() {
  do
    :: detectorSW ->
	  ES_SW ? true;
	  lightSW = green;
	  lightSW = red;
	  ES_SW ! true;
  od;
}

active proctype ControllerES() {
  do
    :: detectorES ->
	  SN_ES ? true;
    ES_SW ? true;
	  ES_NE ? true;
	  lightES = green;
	  lightES = red;
	  SN_ES ! true;
    ES_SW ! true;
	  ES_NE ! true;
  od;
}

active proctype ControllerSN() {
  do
    :: detectorSN ->
	  SN_NE ? true;
	  SN_ES ? true;
    SN_EW ? true;
	  lightSN = green;
	  lightSN = red;
	  SN_NE ! true;
	  SN_ES ! true;
    SN_EW ! true;
  od;
}

ltl safety {
  ([] !(lightNE == green && (lightSN == green || lightEW == green || lightES == green))) &&
  ([] !(lightEW == green && (lightSN == green || lightNE == green))) &&
  ([] !(lightSW == green && (lightES == green))) &&
  ([] !(lightES == green && (lightSN == green || lightSW == green || lightNE == green))) &&
  ([] !(lightSN == green && (lightNE == green || lightES == green || lightEW == green)))
}

ltl fairness {
  ([]<> !(lightNE == green && detectorNE)) &&
  ([]<> !(lightEW == green && detectorEW)) &&
  ([]<> !(lightSW == green && detectorSW)) &&
  ([]<> !(lightES == green && detectorES)) &&
  ([]<> !(lightSN == green && detectorSN))
}

ltl livenessSN {
  ([]<> (lightES == red && lightES == red && lightEW == red)) -> ([] ((detectorSN && lightSN == red) -> <> (lightSN == green)))
}


