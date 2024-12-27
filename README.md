# About

This repository is a formalization, in [Lean](https://lean-lang.org), of [IEEE 754](https://en.wikipedia.org/wiki/IEEE_754#2019) decimal floating-point arithmetic. No, not _binary_ floating-point arithmetic. _Decimal_ arithmetic. Where `"0.1"` and `"0.3"` really are, exactly, 0.1 and 0.3, not a base-2 approximation thereof.

## Motivation

This work was motivated by the effort to [add decimal numbers to JavaScript](https://github.com/tc39/proposal-decimal).

It is not necessary to do a formalization to shepherd a new language feature through [the Ecma TC39 process](https://tc39.es/process-document/). But the details of IEEE 754 can be a bit tricky. And because a feature that goes live in JavaScript essentially lives forever, and impacts a vast user base, it is critical to make sure that we're getting things just right.
