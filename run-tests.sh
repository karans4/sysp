#!/bin/bash
# sysp test runner - compiles and runs all tests with memory checking
# All phases run in parallel using background jobs + wait

TESTS="test-cons test-refcount test-qq test-macros test-macros2 test-infer test-nesting test-numerics test-types test-recur test-union test-deftype test-branch-union test-inline test-match test-mono test-arc test-limitations test-modules test-closures test-threads test-conditions test-ffi test-c99 test-escape test-polish test-hof test-hashmap test-collections test-strings test-variadic test-nth test-asm test-values test-namespaces test-dot test-auto-poly test-generics test-traits test-printable"
CFLAGS="-std=c99 -pedantic -Wall -Wextra -lpthread"
SYSP="sbcl --script sysp.lisp"
TEST_DIR="tests"
BUILD_DIR="tests/build"

mkdir -p "$BUILD_DIR"

echo "=== sysp Test Suite ==="
echo

# --- Compile phase (parallel: sysp + gcc per test) ---
echo "--- Compiling tests ---"
compile_one() {
    local test="$1"
    local src="$TEST_DIR/$test.sysp"
    local c_out="$BUILD_DIR/$test.c"
    local bin="$BUILD_DIR/$test"
    local log="$BUILD_DIR/$test.compile.log"

    if [ ! -f "$src" ]; then
        echo "SKIP $test" > "$log"
        return 0
    fi

    if ! $SYSP "$src" "$c_out" 2>/dev/null; then
        echo "FAIL_SYSP $test" > "$log"
        return 1
    fi

    if ! gcc $CFLAGS "$c_out" -o "$bin" 2>/dev/null; then
        echo "FAIL_GCC $test" > "$log"
        return 1
    fi

    echo "OK $test" > "$log"
    return 0
}

pids=()
for test in $TESTS; do
    compile_one "$test" &
    pids+=($!)
done
wait "${pids[@]}" 2>/dev/null

FAILED=0
for test in $TESTS; do
    log="$BUILD_DIR/$test.compile.log"
    status=$(cat "$log" 2>/dev/null | cut -d' ' -f1)
    case "$status" in
        OK)       echo "  $test: OK" ;;
        FAIL_SYSP) echo "  $test: FAILED (sysp)"; FAILED=$((FAILED + 1)) ;;
        FAIL_GCC)  echo "  $test: FAILED (gcc)";  FAILED=$((FAILED + 1)) ;;
        SKIP)      echo "  $test: skipped" ;;
        *)         echo "  $test: FAILED (unknown)"; FAILED=$((FAILED + 1)) ;;
    esac
done
echo

# --- Run phase (parallel) ---
echo "--- Running tests ---"
PASSED=0

run_one() {
    local test="$1"
    local bin="$BUILD_DIR/$test"
    local out="$BUILD_DIR/$test.out"
    local status_file="$BUILD_DIR/$test.run.status"

    if [ ! -x "$bin" ]; then
        echo "SKIP" > "$status_file"
        return 0
    fi

    if "$bin" > "$out" 2>&1; then
        echo "OK" > "$status_file"
    else
        echo "FAIL" > "$status_file"
    fi
}

pids=()
for test in $TESTS; do
    run_one "$test" &
    pids+=($!)
done
wait "${pids[@]}" 2>/dev/null

for test in $TESTS; do
    status=$(cat "$BUILD_DIR/$test.run.status" 2>/dev/null)
    case "$status" in
        OK)   echo "  $test: OK"; PASSED=$((PASSED + 1)) ;;
        FAIL) echo "  $test: FAILED"; FAILED=$((FAILED + 1)); cat "$BUILD_DIR/$test.out" ;;
        SKIP) ;;
    esac
done
echo

# --- Valgrind phase (parallel, if available) ---
if command -v valgrind &> /dev/null; then
    echo "--- Memory checking with valgrind ---"

    valgrind_one() {
        local test="$1"
        local bin="$BUILD_DIR/$test"
        local log="$BUILD_DIR/$test.valgrind"
        local status_file="$BUILD_DIR/$test.vg.status"

        if [ ! -x "$bin" ]; then
            echo "SKIP" > "$status_file"
            return 0
        fi

        if valgrind --leak-check=full --error-exitcode=1 "$bin" > "$log" 2>&1; then
            echo "OK" > "$status_file"
        elif grep -q "definitely lost" "$log"; then
            leak=$(grep "definitely lost" "$log" | head -1 | grep -oP '\d+ bytes' | head -1)
            echo "LEAK $leak" > "$status_file"
        else
            echo "ERROR" > "$status_file"
        fi
    }

    pids=()
    for test in $TESTS; do
        valgrind_one "$test" &
        pids+=($!)
    done
    wait "${pids[@]}" 2>/dev/null

    for test in $TESTS; do
        status_line=$(cat "$BUILD_DIR/$test.vg.status" 2>/dev/null)
        status=$(echo "$status_line" | cut -d' ' -f1)
        case "$status" in
            OK)   echo "  $test: OK (no leaks)" ;;
            LEAK) echo "  $test: LEAK ($(echo "$status_line" | cut -d' ' -f2-))" ;;
            ERROR) echo "  $test: ERROR" ;;
            SKIP) ;;
        esac
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
