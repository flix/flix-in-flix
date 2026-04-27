---
name: test-case
description: General style for writing test cases for the Flix in Flix project.
---

# Human-Readable Test Summaries

Each test case should start with a short, human-readable comment that captures
what the test is checking. The comment should summarize the overall input and
expected output so that a reader can understand the intent without reading the
full body first.

For example, a unification test might look like this:

```flix
// `List a ~ List Int` unifying to `{ a -> Int }`
@Test
def unification(): Unit = ...
```

And a type-reduction test might look like this:

```flix
// `Element List a -> a`
@Test
def typeReduction(): Unit = ...
```

Prefer behavior-oriented summaries over step-by-step execution notes.

Avoid comments like:

```flix
// `Outer (Inner x)` first reduces `Inner x` and then uses the reduced argument to match `Outer Int32`
@Test
def reduceTypeRecursivelyReducesAssociatedMemberArgumentBeforeLookup(): Unit \ Assert = ...
```

Prefer comments like:

```flix
// constraintEnv: { Inner a ~ Int32, Outer Int32 ~ Bool }
// `Outer (Inner x) -> Bool`
@Test
def reduceTypeRecursivelyReducesAssociatedMemberArgumentBeforeLookup(): Unit \ Assert = ...
```

# Capture Bugs Honestly

If the expected result and the current implementation disagree in a way that
looks like a bug, do not change the test to match the buggy behavior just to
make it pass.

Write the test for the behavior that should hold, and report the bug
separately.
