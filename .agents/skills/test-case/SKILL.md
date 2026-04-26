---
name: test-case
description: General style for writing test cases for the Flix in Flix project.
---

# Including Human Readable Comment Summary

When writing test cases, it is important to include a short, human-readable
comment at the top of the test case what is being done. For example, when
writing a test case for unification, you might include a comment like:

```flix
// `List a ~ List Int` unifying to `{ a -> Int }`
@Test
def unification(): Unit = ...
```

Or when writing a test case for type-reduction, you might include a comment like:

```flix
// `Element List a -> a`
@Test
def typeReduction(): Unit = ...
```

Don't summarize what's the step-by-step process of the test case, but rather
summarize the overall input and expected output of the test case. This makes it
easier for readers to understand the purpose of the test case at a glance,
without having to read through the entire code of the test case.

For example, Don't write:

```flix
// `Outer (Inner x)` first reduces `Inner x` and then uses the reduced argument to match `Outer Int32`
@Test
def reduceTypeRecursivelyReducesAssociatedMemberArgumentBeforeLookup(): Unit \ Assert = ...
```

Instead, write:

```flix
// constraintEnv: { Inner a ~ Int32, Outer Int32 ~ Bool }
// Outer (Inner x) -> Bool
@Test
def reduceTypeRecursivelyReducesAssociatedMemberArgumentBeforeLookup(): Unit \ Assert = ...
```

# If Found a Possible Bug, Don't Write a Test Case That Makes the Test Case Pass

When writing test cases, if you find yourself that the expected output of the 
test case and the output of the output doesn't make sense, don't write a test
case that makes the test case pass. Instead, write a test case that captures the
bug, and report the bug.