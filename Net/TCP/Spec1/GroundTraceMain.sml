val args = CommandLine.arguments()

val ok = ref true

val _ =
    if null args then
      (TextIO.output(TextIO.stdErr,
                     "Usage: "^CommandLine.name() ^
                     " tracefile1 tracefiles\n");
       OS.Process.exit OS.Process.failure)
    else ()
