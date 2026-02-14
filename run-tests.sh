#!/bin/bash
# sysp test runner - compiles and runs all tests with memory checking

set -e

TESTS="test-cons test-refcount test-qq test-macros test-macros2 test-infer test-nesting test-numerics test-types test-recur test-union test-deftype test-branch-union test-inline test-match test-mono test-arc test-limitations test-modules test-closures"
CFLAGS="-std=c99 -pedantic -Wall -Wextra"
SYSP="sbcl --script sysp.lisp"
TEST_DIR="tests"
BUILD_DIR="tests/build"
FAILED=0
PASSED=0

# Create build directory
mkdir -p "$BUILD_DIR"

echo "=== sysp Test Suite ==="
echo

# Compile phase
echo "--- Compiling tests ---"
for test in $TESTS; do
    src="$TEST_DIR/$test.sysp"
    c_out="$BUILD_DIR/$test.c"
    bin="$BUILD_DIR/$test"

    if [ -f "$src" ]; then
        echo -n "Compiling $src... "
        if $SYSP "$src" "$c_out" 2>/dev/null; then
            echo "OK"
        else
            echo "FAILED (sysp)"
            FAILED=$((FAILED + 1))
            continue
        fi

        echo -n "  gcc $test.c... "
        if gcc $CFLAGS "$c_out" -o "$bin" 2>/dev/null; then
            echo "OK"
        else
            echo "FAILED (gcc)"
            FAILED=$((FAILED + 1))
        fi
    else
        echo "Skipping $test (file not found)"
    fi
done
echo

# Run phase
echo "--- Running tests ---"
for test in $TESTS; do
    bin="$BUILD_DIR/$test"
    out="$BUILD_DIR/$test.out"

    if [ -x "$bin" ]; then
        echo -n "Running $test... "
        if "$bin" > "$out" 2>&1; then
            echo "OK"
            PASSED=$((PASSED + 1))
        else
            echo "FAILED (exit code $?)"
            FAILED=$((FAILED + 1))
            cat "$out"
        fi
    fi
done
echo

# Valgrind phase (if available)
if command -v valgrind &> /dev/null; then
    echo "--- Memory checking with valgrind ---"
    for test in $TESTS; do
        bin="$BUILD_DIR/$test"
        log="$BUILD_DIR/$test.valgrind"

        if [ -x "$bin" ]; then
            echo -n "Valgrind $test... "
            if valgrind --leak-check=full --error-exitcode=1 "$bin" > "$log" 2>&1; then
                echo "OK (no leaks)"
            else
                # Check if it's a known leak issue (unbound temporaries)
                if grep -q "definitely lost" "$log"; then
                    LEAK_BYTES=$(grep "definitely lost" "$log" | head -1 | grep -oP '\d+ bytes' | head -1)
                    echo "LEAK ($LEAK_BYTES)"
                else
                    echo "ERROR"
                fi
            fi
        fi
    done
    echo
else
    echo "--- Valgrind not available, skipping memory checks ---"
    echo
fi

# Summary
echo "=== Summary ==="
echo "Passed: $PASSED"
echo "Failed: $FAILED"

if [ $FAILED -gt 0 ]; then
    exit 1
fi
exit 0
