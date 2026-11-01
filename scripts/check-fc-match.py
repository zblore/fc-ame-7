#!/usr/bin/env python3
"""Check that Challenge.lean states Formal Conjectures' two AME(7) statements, and nothing else.

Palomar's Comparator checks that Solution proves the statements of Challenge.lean, with the same
definitions. This script checks the other link: that Challenge.lean is Formal Conjectures' text.

The check is a whitelist, not a search. Challenge.lean must consist of exactly:

* an optional header comment, `module`, `public import Mathlib` and one module docstring;
* `@[expose] public section` and Formal Conjectures' `open scoped BigOperators`;
* `namespace OpenQuantumProblem35`;
* blocks copied from Formal Conjectures' `35.lean`, each identical to one of its blank-line
  separated blocks (definitions with their docstrings, and its section comments), in Formal
  Conjectures' order: exactly the definitions (NEEDED) and the `CoeFun` instance the
  statements need;
  the one exception is DIVERGENCE below, a single proof step inside `combineFirst`;
* the comment `/- ## The statements -/`;
* Formal Conjectures' `ame_7_2_not_exists` and `ame_7_exists_iff`, docstring included, with only
  the `@[category ...]` attribute line left out, and the body `by sorry`;
* `end OpenQuantumProblem35`.

Any other line (a `variable`, `universe`, `open`, `def`, `instance`, `set_option`, `notation`,
`attribute`, ...) fails the check. Header and module-docstring comments may not contain `/-`, so
nested comments cannot hide code. On the Formal Conjectures side, the script checks that nothing
in the whole file before the two statements (a `variable`, `universe`, `omit`, `open`, a
`section`, a notation or macro, an instance other than the two known ones, at any indentation)
could change their meaning.

DIVERGENCE: inside `combineFirst`, Formal Conjectures proves `i.1 - m < n - m` by `omega`. Under
Lean's module system `omega` leaves a private auxiliary lemma whose name contains the module's
name, so Comparator could never match the copy in `Challenge` with the copy in `AME7.Defs`. Both
files use `exact Nat.sub_lt_sub_right him i.2` instead, and the script requires exactly that
replacement. `audit/Audit.lean` must contain Formal Conjectures' original `combineFirst`, renamed
`combineFirstFC`, and check by `rfl` that the two are equal.

`AME7/Defs.lean` must be Formal Conjectures' `35.lean` up to its benchmark statements, with
exactly the documented changes (an added copyright line, `FormalConjecturesUtil` replaced by
`Mathlib`, the `category` and `AMS` attributes removed, DIVERGENCE, a provenance docstring, and a
closing `end`). `AME7/FormalTarget.lean` must state both theorems under Formal Conjectures'
names with Formal Conjectures' signatures. These are regression checks; Comparator is what
guarantees that the proofs agree with Challenge.lean.

Usage:
  check-fc-match.py [FC_CHECKOUT]   check; without an argument, download FC at FC_COMMIT
  check-fc-match.py --self-test [FC_CHECKOUT]
                                    check, then confirm that a list of altered Challenge, Defs,
                                    FormalTarget and Audit files all fail
"""
import re
import sys
import urllib.request
from pathlib import Path

FC_COMMIT = "b6939a3a0d89e5f999fa8c6483a6ef646c1e2923"
SOURCE = "FormalConjectures/OpenQuantumProblems/35.lean"
NAMESPACE = "OpenQuantumProblem35"
THEOREMS = ["ame_7_2_not_exists", "ame_7_exists_iff"]
NEEDED = ["Config", "StateVector", "mkStateVector", "IsNormalized", "permuteConfig",
          "permuteState", "combineFirst", "reducedDensityFirst", "maximallyMixed",
          "HasMaximallyMixedFirstReduction", "IsAME", "ExistsAME"]
INSTANCE_LINE = "instance {n d : ℕ} : CoeFun (StateVector n d) (fun _ => Config n d → ℂ) where"
KNOWN_INSTANCES = [INSTANCE_LINE,
                   "instance {n d : ℕ} : DecidablePred (@IsConstantConfig n d) := by"]
DIVERGENCE = ("        have him : m ≤ i.1 := Nat.le_of_not_gt hi\n        omega⟩",
              "        have him : m ≤ i.1 := Nat.le_of_not_gt hi\n"
              "        exact Nat.sub_lt_sub_right him i.2⟩")
STATEMENTS_MARKER = "/- ## The statements -/"
BENCHMARK_MARKER = "/- ## Solved benchmark cases -/"
CATEGORY_LINE = re.compile(r"^@\[category [^\]]*\]\n", re.M)
# A block comment's body: no `-/` (which would end it) and no `/-` (which would nest).
COMMENT_BODY = r"(?:(?!-/|/-).)*"


def fc_source(root):
    if root is not None:
        return (Path(root) / SOURCE).read_text(encoding="utf-8")
    url = ("https://raw.githubusercontent.com/google-deepmind/formal-conjectures/"
           f"{FC_COMMIT}/{SOURCE}")
    with urllib.request.urlopen(url) as response:
        return response.read().decode("utf-8").replace("\r\n", "\n")


def fc_blocks(fc):
    """Formal Conjectures' blank-line separated blocks inside the namespace, before the
    benchmark statements."""
    start = fc.index(f"namespace {NAMESPACE}\n") + len(f"namespace {NAMESPACE}\n")
    stop = fc.index(BENCHMARK_MARKER)
    return [b for b in diverge(fc[start:stop]).strip("\n").split("\n\n")]


def diverge(text):
    """Formal Conjectures' text with DIVERGENCE applied, which must occur exactly once."""
    if text.count(DIVERGENCE[0]) != 1:
        raise ValueError("FC: the combineFirst step to replace was not found exactly once")
    return text.replace(DIVERGENCE[0], DIVERGENCE[1])


def fc_statement(fc, name):
    """Formal Conjectures' statement, docstring included, without the category line."""
    i = fc.index(f"\ntheorem {name} ") + 1
    j = fc.rfind("/--", 0, i)
    k = fc.index("  sorry\n", i) + len("  sorry")
    between = fc[fc.rfind("\n\n", 0, j) + 2:j]
    if between.strip():
        raise ValueError(f"{name}: unexpected text before its docstring: {between!r}")
    block = fc[j:k]
    if len(CATEGORY_LINE.findall(block)) != 1:
        raise ValueError(f"{name}: expected one category line")
    return CATEGORY_LINE.sub("", block)


def check_fc_context(fc):
    """Nothing before the statements, inside the namespace, may change their meaning."""
    i = fc.index(f"\nnamespace {NAMESPACE}\n")
    pre = fc[:i]
    if [l for l in pre.split("\n") if l.startswith("open")] != ["open scoped BigOperators"]:
        raise ValueError("FC: unexpected open lines before the namespace")
    # The whole file up to the last statement, header and imports included; the one allowed
    # `open` line before the namespace is checked above and dropped here.
    region = fc[:fc.index(f"\ntheorem {THEOREMS[-1]} ")]
    region = region.replace("\nopen scoped BigOperators\n", "\n", 1)
    # The module system's one `@[expose] public section` makes definitions visible and does
    # not change how the statements elaborate; exactly one is allowed, and dropped here.
    if region.count("\n@[expose] public section\n") != 1:
        raise ValueError("FC: expected exactly one `@[expose] public section`")
    region = region.replace("\n@[expose] public section\n", "\n", 1)
    # A context command may sit behind attributes or modifiers (`@[simp] public notation ...`).
    bad = re.findall(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:public|private|protected|noncomputable|"
                     r"unsafe|partial)\s+)*"
                     r"(variable|universe|omit|include|open|section|set_option (?!linter\.)|"
                     r"notation|infix|prefix|postfix|macro|macro_rules|syntax|elab|local|scoped|"
                     r"attribute|namespace (?!" + NAMESPACE + r"\b)).*",
                     region, re.M)
    if bad:
        raise ValueError(f"FC: context lines before the statements: {bad}")
    instances = [l.strip() for l in region.split("\n") if re.match(r"\s*(\S+ )?instance\b", l)]
    if instances != KNOWN_INSTANCES:
        raise ValueError(f"FC: unexpected instances before the statements: {instances}")


def check_challenge(text, fc):
    blocks = fc_blocks(fc)
    s = text
    m = re.match(r"(/-" + COMMENT_BODY + r"-/\n)?module\n\n"
                 r"public import Mathlib\n"
                 r"\n/-!" + COMMENT_BODY + r"-/\n\n@\[expose\] public section\n\n"
                 r"open scoped BigOperators\n\nnamespace " + NAMESPACE + r"\n\n", s, re.S)
    if not m:
        raise ValueError("Challenge: header, imports, docstring or namespace not as expected")
    body = s[m.end():]
    end = f"\nend {NAMESPACE}\n"
    if not body.endswith(end) or body.count(end) != 1:
        raise ValueError("Challenge: must end with the namespace's end, once")
    body = body[:-len(end)]
    if STATEMENTS_MARKER not in body:
        raise ValueError("Challenge: statements marker missing")
    defs_part, stmts_part = body.split(STATEMENTS_MARKER)
    pos = -1
    names = []
    for b in defs_part.strip("\n").split("\n\n"):
        if b not in blocks:
            raise ValueError(f"Challenge: block not in Formal Conjectures: {b[:80]!r}")
        k = blocks.index(b)
        if k <= pos:
            raise ValueError(f"Challenge: block out of Formal Conjectures' order: {b[:80]!r}")
        pos = k
        mm = re.search(r"^(?:noncomputable )?(?:abbrev|def) (\S+)", b, re.M)
        if re.search(r"^(lemma|theorem) ", b, re.M):
            raise ValueError(f"Challenge: copied block is a lemma or theorem: {b[:80]!r}")
        if mm:
            names.append(mm.group(1))
    missing = [n for n in NEEDED if n not in names]
    if missing:
        raise ValueError(f"Challenge: definitions missing: {missing}")
    if names != NEEDED:
        raise ValueError(f"Challenge: definitions beyond those the statements use: "
                         f"{[n for n in names if n not in NEEDED]}")
    instances = [l for l in defs_part.split("\n") if l.startswith("instance")]
    if instances != [INSTANCE_LINE]:
        raise ValueError(f"Challenge: expected exactly the CoeFun instance, found {instances}")
    expected = "\n\n" + "\n\n".join(fc_statement(fc, t) for t in THEOREMS) + "\n"
    if stmts_part != expected:
        raise ValueError("Challenge: statements differ from Formal Conjectures'")


def expected_defs(fc, defs_text):
    """Defs.lean as the documented transformation of Formal Conjectures' file."""
    body = diverge(fc[:fc.index(BENCHMARK_MARKER)]).rstrip("\n")
    hdr = "Copyright 2026 The Formal Conjectures Authors.\n"
    body = body.replace(hdr, hdr + "Modifications copyright 2026 Zayn Blore.\n", 1)
    body = body.replace("public import FormalConjecturesUtil\n", "public import Mathlib\n", 1)
    body = CATEGORY_LINE.sub("", body)
    body = body.replace("@[simp, category API, AMS 5 15 81 94]", "@[simp]")
    m = re.search(r"\n/-!\n## Provenance\n" + COMMENT_BODY + r"-/\n", defs_text, re.S)
    if not m:
        raise ValueError("Defs: provenance docstring missing")
    anchor = "\n@[expose] public section\n"
    body = body.replace(anchor, m.group(0) + anchor, 1)
    return body + f"\n\nend {NAMESPACE}\n"


def check_defs(defs_text, fc):
    if re.search(r"@\[[^\]]*(category|AMS)", defs_text):
        raise ValueError("Defs: a category or AMS attribute is left")
    if defs_text != expected_defs(fc, defs_text):
        raise ValueError("Defs: differs from Formal Conjectures beyond the documented changes")


def check_target(target, fc):
    m = re.search(r"\nnamespace " + NAMESPACE + r"\n(.*)\nend " + NAMESPACE + r"\n", target, re.S)
    if not m:
        raise ValueError("FormalTarget: no OpenQuantumProblem35 block")
    block = m.group(1)
    for t in THEOREMS:
        sig = re.search(r"^theorem " + re.escape(t) + r" .*?:=", fc_statement(fc, t), re.M | re.S)
        sig = sig.group(0)[:-2].rstrip() if sig else None
        if not sig or len(re.findall(r"^" + re.escape(sig) + r" :=", block, re.M)) != 1:
            raise ValueError(f"FormalTarget: {t} not stated with Formal Conjectures' signature")
    if re.search(r"^(variable|universe|open|section|set_option)", block, re.M):
        raise ValueError("FormalTarget: context lines in the OpenQuantumProblem35 block")


def check_audit(audit, fc):
    start = fc.index("/--\nMerge a configuration on the first")
    end = fc.index(DIVERGENCE[0]) + len(DIVERGENCE[0])
    original = fc[start:end].replace("def combineFirst ", "def combineFirstFC ", 1)
    if audit.count(original) != 1:
        raise ValueError("Audit: Formal Conjectures' original combineFirst is missing or altered")
    if audit.count("\nexample : @combineFirstFC = @combineFirst := rfl\n") != 1:
        raise ValueError("Audit: the rfl check of combineFirst is missing")


def run(fc, challenge, defs, target, audit):
    check_fc_context(fc)
    check_challenge(challenge, fc)
    check_defs(defs, fc)
    check_target(target, fc)
    check_audit(audit, fc)


def mutations(challenge, defs, target, audit):
    c, d, t, a = challenge, defs, target, audit
    yield "def body changed", c.replace("  ‖ψ‖ = 1", "  ‖ψ‖ ≤ 1", 1), d, t, a
    yield "statement changed", c.replace("↔ 3 ≤ d := by", "↔ 4 ≤ d := by", 1), d, t, a
    yield "hypothesis dropped", c.replace("(d : ℕ) (hd : 2 ≤ d) : ExistsAME 7 d",
                                          "(d : ℕ) : ExistsAME 7 d", 1), d, t, a
    yield "extra definition", c.replace(STATEMENTS_MARKER,
                                        "def ExistsAME' (n d : ℕ) : Prop := True\n\n"
                                        + STATEMENTS_MARKER, 1), d, t, a
    yield "variable added", c.replace(STATEMENTS_MARKER,
                                      "variable {n : ℕ}\n\n" + STATEMENTS_MARKER, 1), d, t, a
    yield "set_option added", c.replace("namespace " + NAMESPACE + "\n",
                                        "namespace " + NAMESPACE + "\n\nset_option "
                                        "autoImplicit true\n", 1), d, t, a
    yield "instance added", c.replace(STATEMENTS_MARKER,
                                      "instance : Inhabited (Config 7 2) := ⟨fun _ => 0⟩\n\n"
                                      + STATEMENTS_MARKER, 1), d, t, a
    yield "attribute added", c.replace(STATEMENTS_MARKER,
                                       "attribute [simp] IsAME\n\n" + STATEMENTS_MARKER, 1), d, t, a
    yield "nested comment in docstring", c.replace(
        "/-!\n# Seven-party", "/-!\n/- -/ def X := 1\n# Seven-party", 1), d, t, a
    yield "non-Mathlib import", c.replace(
        "public import Mathlib\n", "public import Mathlib\npublic import AME7.Defs\n", 1), d, t, a
    yield "open added", c.replace("open scoped BigOperators\n",
                                  "open scoped BigOperators\nopen Real\n", 1), d, t, a
    yield "definition dropped", c.replace(
        c[c.index("/-- Existence of an"):c.index(STATEMENTS_MARKER)], "", 1), d, t, a
    yield "lemma copied in", c.replace(
        STATEMENTS_MARKER,
        "/-- A state built from amplitudes has those amplitudes as its coordinates. -/\n"
        "@[simp]\nlemma mkStateVector_apply {n d : ℕ} (ψ : Config n d → ℂ) (x : Config n d) :\n"
        "    mkStateVector ψ x = ψ x := rfl\n\n" + STATEMENTS_MARKER, 1), d, t, a
    yield "Defs proof changed", c, d.replace("  ‖ψ‖ = 1", "  ‖ψ‖ = 1 ∨ False", 1), t, a
    yield "Defs attribute kept", c, d.replace("@[simp]\nlemma mkStateVector_apply",
                                              "@[simp, category API, AMS 5 15 81 94]\n"
                                              "lemma mkStateVector_apply", 1), t, a
    yield "Defs lemma added", c, d.replace(f"\nend {NAMESPACE}\n",
                                           "\ntheorem extra : True := trivial\n\nend "
                                           + NAMESPACE + "\n", 1), t, a
    # the same signature also heads `AME7.ame_7_exists_iff`; alter the copy in the FC block
    head, sep, tail = t.rpartition("namespace " + NAMESPACE + "\n")
    yield "FormalTarget statement changed", c, d, head + sep + tail.replace(
        "(hd : 2 ≤ d) : ExistsAME 7 d ↔ 3 ≤ d :=",
        "(hd : 3 ≤ d) : ExistsAME 7 d ↔ 3 ≤ d :=", 1), a
    yield "FormalTarget variable added", c, d, t.replace(
        "namespace " + NAMESPACE + "\n\n/-- Formal Conjectures' `ame_7_2",
        "namespace " + NAMESPACE + "\n\nvariable {n : ℕ}\n\n/-- Formal Conjectures' `ame_7_2", 1), a
    yield "omega restored", c.replace(DIVERGENCE[1], DIVERGENCE[0], 1), d, t, a
    coe_start = c.index("/-- A state vector can be evaluated")
    coe_end = c.index("/-- A state vector is normalized")
    yield "instance dropped", c.replace(c[coe_start:coe_end], "", 1), d, t, a
    yield "Defs omega restored", c, d.replace(DIVERGENCE[1], DIVERGENCE[0], 1), t, a
    yield "Audit original changed", c, d, t, a.replace(
        DIVERGENCE[0], DIVERGENCE[1], 1)
    yield "Audit rfl check dropped", c, d, t, a.replace(
        "\nexample : @combineFirstFC = @combineFirst := rfl\n", "\n", 1)
    yield "Mathlib submodule import", c.replace(
        "public import Mathlib\n", "public import Mathlib.Logic.Basic\npublic import Mathlib\n",
        1), d, t, a
    yield "extra FC definition", with_extra_fc_block(c, "def leftIndex "), d, t, a


def with_extra_fc_block(c, head):
    """Challenge with one more of Formal Conjectures' own definition blocks, in FC's order."""
    blocks = fc_blocks(FC_TEXT)
    k = next(i for i, b in enumerate(blocks) if head in b)
    defs_part, rest = c.split(STATEMENTS_MARKER)
    ours = defs_part.strip("\n").split("\n\n")
    pos = next(j for j, b in enumerate(ours) if b in blocks and blocks.index(b) > k)
    ours.insert(pos, blocks[k])
    start = c.index(defs_part.strip("\n"))
    return c[:start] + "\n\n".join(ours) + "\n\n" + STATEMENTS_MARKER + rest


def fc_context_mutations(fc):
    """Formal Conjectures files whose context could change the statements."""
    ns = f"\nnamespace {NAMESPACE}\n"
    yield "FC variable before the namespace", fc.replace(ns, "\nvariable {d : ℕ}\n" + ns, 1)
    yield "FC notation before the namespace", fc.replace(
        ns, "\nnotation \"‖\" x \"‖\" => x\n" + ns, 1)
    yield "FC set_option before the namespace", fc.replace(
        ns, "\nset_option autoImplicit true\n" + ns, 1)
    yield "FC public notation before the namespace", fc.replace(
        ns, "\npublic notation \"‖\" x \"‖\" => x\n" + ns, 1)
    yield "FC attributed macro before the namespace", fc.replace(
        ns, "\n@[inherit_doc] private macro \"zz\" : term => `(0)\n" + ns, 1)


def main():
    args = sys.argv[1:]
    self_test = "--self-test" in args
    args = [a for a in args if a != "--self-test"]
    root = args[0] if args else None
    here = Path(__file__).resolve().parent.parent
    challenge = (here / "Challenge.lean").read_text(encoding="utf-8")
    defs = (here / "AME7" / "Defs.lean").read_text(encoding="utf-8")
    target = (here / "AME7" / "FormalTarget.lean").read_text(encoding="utf-8")
    audit = (here / "audit" / "Audit.lean").read_text(encoding="utf-8")
    fc = fc_source(root)
    global FC_TEXT
    FC_TEXT = fc
    run(fc, challenge, defs, target, audit)
    print(f"OK: Challenge.lean, AME7/Defs.lean, AME7/FormalTarget.lean and audit/Audit.lean "
          f"match Formal Conjectures at {FC_COMMIT[:8]}")
    if not self_test:
        return
    n = 0
    for label, c, d, t, a in mutations(challenge, defs, target, audit):
        if (c, d, t, a) == (challenge, defs, target, audit):
            sys.exit(f"self-test: mutation '{label}' changed nothing")
        try:
            run(fc, c, d, t, a)
        except ValueError:
            n += 1
            continue
        sys.exit(f"self-test: mutation '{label}' passed the check")
    for label, f in fc_context_mutations(fc):
        if f == fc:
            sys.exit(f"self-test: mutation '{label}' changed nothing")
        try:
            check_fc_context(f)
        except ValueError:
            n += 1
            continue
        sys.exit(f"self-test: mutation '{label}' passed the context check")
    print(f"OK: self-test, all {n} altered files fail")


if __name__ == "__main__":
    main()
