@echo off
setlocal
if not exist .work mkdir .work
where cl >nul 2>&1
if errorlevel 1 (
  for /f "usebackq delims=" %%I in (`"%ProgramFiles(x86)%\Microsoft Visual Studio\Installer\vswhere.exe" -latest -products * -requires Microsoft.VisualStudio.Component.VC.Tools.x86.x64 -property installationPath`) do call "%%I\VC\Auxiliary\Build\vcvars64.bat" >nul
)
cl /nologo /EHsc /std:c++20 /O2 /Fo.work\minimax.obj /Fe.work\minimax.exe minimax.cpp
if errorlevel 1 exit /b 1
if /I "%~1"=="fixed" exit /b 0
cl /nologo /EHsc /std:c++20 /O2 /Fo.work\minimax_fast.obj /Fe.work\minimax_fast.exe minimax_fast.cpp
if errorlevel 1 exit /b 1
cl /nologo /EHsc /std:c++20 /O2 /Fo.work\potential.obj /Fe.work\potential.exe potential.cpp
exit /b %errorlevel%
