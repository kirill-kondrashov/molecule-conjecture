#!/bin/bash
set -euo pipefail

# File paths
README="README.md"
EXPECTED="expected.txt"
ACTUAL="output.txt"

# Extract the expected output block from README.md.
# Prefer explicit markers when present; fall back to the legacy heading-based
# extraction so older README layouts still work.
if grep -q "EXPECTED_CHECK_OUTPUT_START" "$README"; then
  awk '
    /EXPECTED_CHECK_OUTPUT_START/ { found = 1; next }
    /EXPECTED_CHECK_OUTPUT_END/ { exit }
    found && /^```$/ { inblock = !inblock; next }
    found && inblock { print }
  ' "$README" > "$EXPECTED"
else
  awk '
    BEGIN { found = 0; inblock = 0 }
    tolower($0) ~ /expected output/ { found = 1; next }
    found && /^```$/ {
      if (inblock == 0) { inblock = 1; next }
      else { exit }
    }
    inblock { print }
  ' "$README" > "$EXPECTED"
fi

if [ ! -s "$EXPECTED" ]; then
    echo "Failed to extract expected output block from $README"
    exit 1
fi

# Run make check and capture output
# We filter out lines starting with "lake" or containing progress bars if necessary
# Assuming the relevant output is at the end.
echo "Re-running make check..."
make check > "$ACTUAL" 2>&1
EXIT_CODE=$?

if [ $EXIT_CODE -ne 0 ]; then
    echo "make check failed with exit code $EXIT_CODE"
    cat "$ACTUAL"
    exit $EXIT_CODE
fi

# Print the full output for debugging/logs
cat "$ACTUAL"

# Extract the relevant part from the actual output
# We look for the line starting with "✅" or "⚠️" and everything after
grep -A 100 -E "✅|⚠️" "$ACTUAL" > actual_cleaned.txt
mv actual_cleaned.txt "$ACTUAL"

# Compare
if diff -w "$EXPECTED" "$ACTUAL"; then
    echo "Verification successful: Output matches README."
    rm "$EXPECTED" "$ACTUAL"
    exit 0
else
    echo "Verification failed: Output differs from README."
    echo "Expected:"
    cat "$EXPECTED"
    echo "Actual:"
    cat "$ACTUAL"
    rm "$EXPECTED" "$ACTUAL"
    exit 1
fi
