1) unzip fop-v2006.09.10.zip -or- a newer version from http://www.cs.utexas.edu/~schwartz/ATS.html

2) copy the content of fop_wrapper in same directory

3) switch to directory fop\ahead\


install the AHEAD Tool Suite (fop\release\README.html)
this simply means to install cygwin and ant and set path variables


4) call create_mixin.sh to compile mixin.jar -or- "ant -f wrapper.xml mixin"

5) call create_jak2java.sh to compile jak2java.jar -or- "ant -f wrapper.xml jak2java"


the generated files are found in fop\ahead\build\lib\
