#!/usr/bin/env python3
"""sysp-import — Convert C headers to sysp extern/struct/enum/deftype bindings.

Usage: sysp-import <header.h> [--include-dir DIR]...
       sysp-import /usr/include/SDL2/SDL.h > lib/sdl2.sysp

Requires: pip install libclang
"""

import sys
import os
from clang.cindex import (
    Index, CursorKind, TypeKind, TranslationUnit
)

# C type → sysp type mapping
TYPE_MAP = {
    TypeKind.VOID: ":void",
    TypeKind.BOOL: ":bool",
    TypeKind.CHAR_U: ":char",
    TypeKind.UCHAR: ":u8",
    TypeKind.CHAR_S: ":char",
    TypeKind.SCHAR: ":i8",
    TypeKind.SHORT: ":short",
    TypeKind.USHORT: ":u16",
    TypeKind.INT: ":int",
    TypeKind.UINT: ":uint",
    TypeKind.LONG: ":long",
    TypeKind.ULONG: ":ulong",
    TypeKind.LONGLONG: ":i64",
    TypeKind.ULONGLONG: ":u64",
    TypeKind.FLOAT: ":float",
    TypeKind.DOUBLE: ":double",
}

# Named type overrides (from typedefs)
NAMED_TYPE_MAP = {
    "size_t": ":u64",
    "ssize_t": ":i64",
    "ptrdiff_t": ":i64",
    "intptr_t": ":i64",
    "uintptr_t": ":u64",
    "int8_t": ":i8",
    "int16_t": ":i16",
    "int32_t": ":i32",
    "int64_t": ":i64",
    "uint8_t": ":u8",
    "uint16_t": ":u16",
    "uint32_t": ":u32",
    "uint64_t": ":u64",
    "FILE": ":ptr-void",  # opaque
}


def map_type(clang_type):
    """Map a clang type to sysp type string."""
    kind = clang_type.kind

    # Pointer types
    if kind == TypeKind.POINTER:
        pointee = clang_type.get_pointee()
        inner = map_type(pointee)
        if inner == ":void":
            return ":ptr-void"
        if inner == ":char":
            return ":ptr-char"
        # :ptr-X for known types, :ptr-void for complex
        if inner.startswith(":"):
            return f":ptr{inner[1:]}"  # :int → :ptr-int
        return ":ptr-void"

    # Elaborated / typedef — check spelling first
    if kind in (TypeKind.TYPEDEF, TypeKind.ELABORATED):
        name = clang_type.spelling
        # Strip qualifiers
        name = name.replace("const ", "").replace("volatile ", "").strip()
        if name in NAMED_TYPE_MAP:
            return NAMED_TYPE_MAP[name]
        # Check canonical type
        canon = clang_type.get_canonical()
        if canon.kind != kind:
            return map_type(canon)
        # Struct/enum by name
        if name.startswith("struct "):
            return f":ptr-{name[7:]}"
        if name.startswith("enum "):
            return ":int"
        return ":int"  # fallback for unknown typedefs

    # Array → pointer
    if kind in (TypeKind.CONSTANTARRAY, TypeKind.INCOMPLETEARRAY, TypeKind.VARIABLEARRAY):
        elem = map_type(clang_type.element_type)
        if elem.startswith(":"):
            return f":ptr{elem[1:]}"
        return ":ptr-void"

    # Function pointer
    if kind == TypeKind.FUNCTIONPROTO:
        return ":ptr-void"

    # Record (struct/union used directly)
    if kind == TypeKind.RECORD:
        name = clang_type.spelling
        if name.startswith("struct "):
            name = name[7:]
        return f":ptr-{name}" if name else ":ptr-void"

    # Enum
    if kind == TypeKind.ENUM:
        return ":int"

    # Direct lookup
    if kind in TYPE_MAP:
        return TYPE_MAP[kind]

    return ":int"  # safe fallback


def is_from_file(cursor, header_path):
    """Check if cursor is from the target header (not an include)."""
    loc = cursor.location
    if loc.file is None:
        return False
    return os.path.realpath(loc.file.name) == header_path


def emit_function(cursor):
    """Emit (extern name [params] :ret) for a function declaration."""
    name = cursor.spelling
    if name.startswith("_"):
        return None  # skip internal/private

    params = []
    for i, arg in enumerate(cursor.get_arguments()):
        aname = arg.spelling or f"p{i}"
        atype = map_type(arg.type)
        params.append(f"{aname} {atype}")

    ret = map_type(cursor.result_type)
    param_str = " ".join(params) if params else ""
    return f"(extern {name} [{param_str}] {ret})"


def emit_struct(cursor):
    """Emit (struct Name [fields...]) for a struct definition."""
    name = cursor.spelling
    if not name or name.startswith("_"):
        return None

    fields = []
    for field in cursor.type.get_fields():
        fname = field.spelling
        ftype = map_type(field.type)
        fields.append(f"{fname} {ftype}")

    if not fields:
        return None

    field_str = ", ".join(fields)
    return f"(struct {name} [{field_str}])"


def emit_enum(cursor):
    """Emit (enum Name (Variant val) ...) for an enum."""
    name = cursor.spelling
    if not name or name.startswith("_"):
        return None

    variants = []
    for child in cursor.get_children():
        if child.kind == CursorKind.ENUM_CONSTANT_DECL:
            variants.append(f"({child.spelling} {child.enum_value})")

    if not variants:
        return None

    variant_str = " ".join(variants)
    return f"(enum {name} {variant_str})"


def emit_typedef(cursor):
    """Emit (deftype Name type-expr) for a typedef."""
    name = cursor.spelling
    if name.startswith("_") or name in NAMED_TYPE_MAP:
        return None

    underlying = cursor.underlying_typedef_type
    # Skip function pointer typedefs and complex types
    canon = underlying.get_canonical()
    if canon.kind == TypeKind.FUNCTIONPROTO:
        return None
    if canon.kind == TypeKind.POINTER and canon.get_pointee().kind == TypeKind.FUNCTIONPROTO:
        return None  # function pointer typedef

    mapped = map_type(underlying)
    if mapped == ":int" and underlying.spelling == name:
        return None  # self-referential or unresolvable
    return f"(deftype {name} {mapped})"


def import_header(header_path, include_dirs=None):
    """Parse a C header and emit sysp bindings."""
    header_path = os.path.realpath(header_path)

    args = ["-x", "c", "-std=c11"]
    for d in (include_dirs or []):
        args.extend(["-I", d])
    # Add directory containing the header
    args.extend(["-I", os.path.dirname(header_path)])

    index = Index.create()
    tu = index.parse(header_path, args=args,
                     options=TranslationUnit.PARSE_SKIP_FUNCTION_BODIES |
                             TranslationUnit.PARSE_DETAILED_PROCESSING_RECORD)

    if not tu:
        print(f"Error: could not parse {header_path}", file=sys.stderr)
        sys.exit(1)

    header_name = os.path.basename(header_path)
    print(f";; {header_name} — auto-generated by sysp-import")
    print(f";; Source: {header_path}")
    print()

    includes = set()
    structs = []
    enums = []
    typedefs = []
    functions = []

    for cursor in tu.cursor.get_children():
        if not is_from_file(cursor, header_path):
            continue

        if cursor.kind == CursorKind.FUNCTION_DECL:
            result = emit_function(cursor)
            if result:
                functions.append(result)

        elif cursor.kind == CursorKind.STRUCT_DECL:
            if cursor.is_definition():
                result = emit_struct(cursor)
                if result:
                    structs.append(result)

        elif cursor.kind == CursorKind.ENUM_DECL:
            if cursor.is_definition():
                result = emit_enum(cursor)
                if result:
                    enums.append(result)

        elif cursor.kind == CursorKind.TYPEDEF_DECL:
            result = emit_typedef(cursor)
            if result:
                typedefs.append(result)

    # Emit includes
    print(f'(include "{header_name}")')
    print()

    # Emit in order: structs, enums, typedefs, functions
    if structs:
        print(";; Structs")
        for s in structs:
            print(s)
        print()

    if enums:
        print(";; Enums")
        for e in enums:
            print(e)
        print()

    if typedefs:
        print(";; Type aliases")
        for t in typedefs:
            print(t)
        print()

    if functions:
        print(";; Functions")
        for f in functions:
            print(f)

    # Summary to stderr
    total = len(structs) + len(enums) + len(typedefs) + len(functions)
    print(f"\n;; Total: {len(structs)} structs, {len(enums)} enums, "
          f"{len(typedefs)} typedefs, {len(functions)} functions",
          file=sys.stderr)


def main():
    if len(sys.argv) < 2:
        print("Usage: sysp-import <header.h> [--include-dir DIR]...", file=sys.stderr)
        sys.exit(1)

    header = sys.argv[1]
    include_dirs = []
    i = 2
    while i < len(sys.argv):
        if sys.argv[i] == "--include-dir" and i + 1 < len(sys.argv):
            include_dirs.append(sys.argv[i + 1])
            i += 2
        else:
            print(f"Unknown argument: {sys.argv[i]}", file=sys.stderr)
            sys.exit(1)

    if not os.path.exists(header):
        print(f"Error: {header} not found", file=sys.stderr)
        sys.exit(1)

    import_header(header, include_dirs)


if __name__ == "__main__":
    main()
