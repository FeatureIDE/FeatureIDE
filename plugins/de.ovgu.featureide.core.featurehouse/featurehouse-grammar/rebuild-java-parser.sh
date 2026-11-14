#!/bin/sh
# Regenerates FeatureHouse's Java parser (de.ovgu.cide.fstgen.parsers.generated_java15)
# from java15.jj and replaces the parser classes inside ../lib/FeatureHouse.jar.
#
# FeatureHouse.jar bundles the patched JavaCC (org.javacc.parser.Main) that FSTGen
# uses, so only a JDK (javac + jar) is required.
#
# Usage: sh rebuild-java-parser.sh
set -e

HERE="$(cd "$(dirname "$0")" && pwd)"
JAR="$HERE/../lib/FeatureHouse.jar"
PKG=de/ovgu/cide/fstgen/parsers/generated_java15
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

mkdir -p "$WORK/src/$PKG" "$WORK/classes/$PKG"
cp "$HERE/java15.jj" "$WORK/java15.jj"

# 1. Generate Java15Parser, Java15ParserConstants and Java15ParserTokenManager.
java -cp "$JAR" org.javacc.parser.Main -OUTPUT_DIRECTORY="$WORK/src/$PKG" "$WORK/java15.jj"

# 2. Compile against the rest of FeatureHouse (Token, CharStream, AbstractFSTParser, ...).
#    The existing SimplePrintVisitor of this package does not reference the token
#    constants, so it does not need to be recompiled.
#    Java 21 is the Java version required by FeatureIDE (see FHJavaVersionTest).
javac --release 21 -nowarn -encoding UTF-8 -cp "$JAR" -d "$WORK/classes" "$WORK/src/$PKG"/*.java

# 3. Replace the parser classes and the bundled grammar inside (a copy of) the jar.
cp "$WORK/java15.jj" "$WORK/classes/$PKG/java15.jj"
java "$HERE/UpdateJar.java" "$JAR" "$WORK/FeatureHouse.jar" "$WORK/classes/$PKG" "$PKG" SimplePrintVisitor.class
if ! cp "$WORK/FeatureHouse.jar" "$JAR"; then
	echo "Could not overwrite $JAR - close Eclipse (or any process using the jar) and run again." >&2
	exit 1
fi

echo "Updated $JAR"
