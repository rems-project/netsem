Globals.interactive := false;
Globals.print_thy_loads := true;
HOL_Interactive.toggle_quietdec();
load "DiskThms";
load "strings";
load "testEval";
use "CheckTraces.sml";
val _ = PolyML.export("CheckTraces", main)
