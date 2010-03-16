#!/bin/zsh
ml-yacc tiger.grm
echo "CM.make \"sources.cm\";\n use \"export.sml\";\n" | sml
for file in `ls expectcases`
do
  echo "\nTesting $file"
  diff <(sml @SMLload=executable.x86-linux testcases/$file) expectcases/$file
done
