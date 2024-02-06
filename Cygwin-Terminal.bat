@echo off

set ISA_HOME=C:\Daten\UNI_Lisa\Software\Isabelle2023
set TEMP_WINDOWS=%TEMP%
set HOME=%HOMEDRIVE%%HOMEPATH%
set PATH=%ISA_HOME%\bin;%PATH%
set LANG=en_US.UTF-8
set CHERE_INVOKING=true

echo This is the GNU Bash interpreter of Cygwin.
echo Use command "isabelle" to invoke Isabelle tools.
"%ISA_HOME%\contrib\cygwin\bin\bash" --login -i
