#!/usr/bin/env bash

if ! [[ "$0" =~ tla2tex.sh ]]; then
  echo "must be run from repository root"
  exit 255
fi

function strip_tla_tex {
  local file="$1"
  local start_pattern="\begin{document}"
  local end_pattern="\@x{}\bottombar\@xx{}%"

  # Use grep to find starting and ending line numbers
  start_line=$(grep -nF "$start_pattern" "$file" | cut -d: -f1)
  end_line=$(grep -nF "$end_pattern" "$file" | cut -d: -f1)

  awk "NR > ${start_line} && NR <= ${end_line}" ${file} > ${file}.tmp
  mv ${file}.tmp ${file}
}


WORKDIR="$(mktemp -d)"
trap 'rm -rf -- "$WORKDIR"' EXIT

if [ "${TLA_TOOL}" ]; then 
    cp ${TLA_TOOL}/tla2tools.jar ${WORKDIR}
else
    echo -n "Downloading TLA+ tools ... "
    wget -qN https://nightly.tlapl.us/dist/tla2tools.jar -P ${WORKDIR}
fi

cp algo/*.tex ${WORKDIR}
cp tla//extendedraft.tla ${WORKDIR}

pushd ${WORKDIR}
for filename in $(find . -maxdepth 1 -type f \( -name "*.tex" -and -not -name "extendedraft.tex" -and -not -name tlatex.tex \) )
do
    java -cp tla2tools.jar tla2tex.TeX $filename 
done

java -cp tla2tools.jar tla2tex.TLA ./extendedraft.tla
strip_tla_tex ./extendedraft.tex
popd

cp ${WORKDIR}/*.tex algo/
rm -rf ${WORKDIR}




