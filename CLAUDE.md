# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build Commands

- `lake build` - Build the Lean project
- `lake exe cache get` - Download mathlib cache (recommended before first build for faster compilation)
- `lake update` - Update dependencies
- `npm run format` - Format code with Prettier
- `npm run lint` - Check code formatting

## Architecture

This is a Lean 4 library implementing IEEE 754 decimal128 floating-point arithmetic. The project is motivated by the JavaScript decimal proposal.

### Module Structure

- `Decimal128.lean` - Root module that imports Decimal128.Basic
- `Decimal128/Basic.lean` - Core types and definitions
  - Defines `DecimalValue` enum with NaN, ±Infinity, ±Zero, and Rational values
  - Defines `SuitableRationals` - rationals that fit within decimal128 constraints
- `Decimal128/Constants.lean` - IEEE 754 decimal128 constants
- `Decimal128/Arithmetic.lean` - Arithmetic operations
- `Decimal128/Comparisons.lean` - Comparison operations  
- `Decimal128/Theorems.lean` - Mathematical theorems and proofs

The library uses Mathlib extensively for mathematical foundations. Testing is done through Lean's proof system rather than traditional unit tests.

## Development Setup

1. Ensure Lean 4 is installed (uses v4.20.0-rc5)
2. Run `lake exe cache get` to download mathlib cache
3. Run `lake build` to build the project
4. Optional: Run `npm install` if you need formatting tools