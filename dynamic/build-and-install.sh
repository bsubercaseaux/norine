#!/bin/bash


if [ -t 1 ]; then
	reset="\033[0m"
	 bold="\033[1m"
	  red="\033[91m"
	green="\033[32m"
fi

msg() {
	msgcol=$green
	if [ "${2-""}" = "err" ] ; then
		msgcol=$red
	fi
	echo -e "\n${bold}--norine-- build-and-install.sh:${reset}${msgcol} $1${reset}\n"
}


usage () {
cat <<EOF
usage: build-and-install.sh [-h|--help][-g|--debug][-s|--glasgow][-l|--local][-c|--cmake][-p|--pip]

-h | --help     print this command line option summary
-g | --debug    compile in debug mode, with assertion checking and symbols
-c | --cmake   	use this cmake command (default: cmake)
EOF
}

debug=0
loc_inst=0

CMAKE_CMD="cmake"
CMAKE_BUILD_DIR="build"
CMAKE_FLAGS=(-B "$CMAKE_BUILD_DIR" "-S" ".")
CMAKE_BUILD_PARALLEL_LEVEL=$(nproc --all)
export CMAKE_BUILD_PARALLEL_LEVEL
CONF_FLAGS=("-fPIC")


while [ $# -gt 0 ]
do
  case $1 in
    -h|--help)    usage; exit 0;;
    -g|--debug)   debug=1;;
    -c|--cmake)   if [ $# -eq 1 ]; then msg "expecting cmake command after '$1'" "err" && exit 1; else shift; CMAKE_CMD="$1"; fi;;
    *) msg "invalid option '$1' (try '-h')" "err" && exit 1;;
  esac
  shift
done

if [ $debug = 1 ]; then
	msg "Build type set to DEBUG"
	CMAKE_FLAGS+=("-DCMAKE_BUILD_TYPE=Debug")
	CONF_FLAGS+=("-g")
else
	msg "Build type set to RELEASE"
fi

#!/usr/bin/env bash
set -e

CADICAL_COMMIT=f13d74439a5b5c963ac5b02d05ce93a8098018b8
CADICAL_DIR=cadical

if [ ! -d "$CADICAL_DIR" ]; then
    echo "Cloning CaDiCaL..."
    git clone https://github.com/arminbiere/cadical.git "$CADICAL_DIR"
fi

cd "$CADICAL_DIR"

echo "Checking out fixed commit..."
git fetch
git checkout "$CADICAL_COMMIT"

echo "CaDiCaL installed successfully."

cd ..


if [ ! -d "$CADICAL_DIR" ]; then
	msg "CaDiCaL expected at $CADICAL_DIR, but the directory does not exist" "err"
	exit 1
else
	msg "Building CaDiCaL"
	if [ -z "$(ls "$CADICAL_DIR")" ]; then
		echo "empty"
		git submodule init
		git submodule update
	fi
	cd "$CADICAL_DIR" || { msg "cannot cd to '$CADICAL_DIR', exiting" "err" ; exit ; }
	if [ ! -d "build" ] || [ ! -f "build/makefile" ] || [ ! -f "makefile" ]; then
		./configure "${CONF_FLAGS[@]}" || { msg "CaDiCaL 'configure' failed, exiting" "err" ; exit ; }
	fi
	make -j"$CMAKE_BUILD_PARALLEL_LEVEL" || { msg "CaDiCaL 'make' failed, exiting" "err" ; exit ; }
	cd .. || exit
fi

msg "Configuring norine build directory..."
"$CMAKE_CMD" "${CMAKE_FLAGS[@]}"

msg "building norine"
if "$CMAKE_CMD" --build "$CMAKE_BUILD_DIR"; then
	msg "norine built successfully"
else
	msg "Unable to build norine, exiting" "err"
	exit 1;
fi
