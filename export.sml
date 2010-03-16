SMLofNJ.exportFn (
  "executable",
  fn (cmd : string, files) =>
    (map (fn (file) =>
           PrintAbsyn.print (TextIO.stdOut, Parse.parse file)) files;
           OS.Process.success));
