| Band | Value | Meaning |
|---|---|---|
| `BLOCK_CONTRACT` | `Long.MIN_VALUE` | apply a block/loop contract instead of executing the block |
| `LOOP_INVARIANT` | −20000 | apply a loop invariant instead of unrolling |
| `CLOSE` | −15000 | close the goal (eager closure is completeness-neutral) |
| `REWRITE` | −11000 | one-step simplification and decidable ground rewrites (`concrete`) |
| `SUBST` | −10000 | force a pending substitution / eager equality (`try_apply_subst`) |
| `ELIMINATE` | −8000 | eliminate updates and literals |
| `DECOMPOSE` | −7000 | non-splitting sequent decomposition (alpha rules, update-apply-on-update) |
| `TYPE` | −6000 | type reasoning (delta rules, type hierarchy) |
| `NORMALIZE` | −5000 | canonicalize / order / commute terms |
| `SIMPLIFY` | −4500 | safe, size-reducing definitional simplification and SE steps |
| `EXECUTE` | −4000 | a symbolic-execution program step / state merge |
| `SOLVE` | −3000 | solve direct (in)equations; apply query axioms |
| `ENLARGE` | −2000 | useful but size-increasing simplification (e.g. comprehension / map unfolding) |
| `PREFER` | −500 | minor local structural preference |
| `DEFAULT` | 0 | no strategic bias — apply in due (age) order |
| `DEFER` | 500 | lazy definitional unfolding, applied only when needed |
| `DEFER_STRONG` | 10000 | strongly defer |
| `LAST_RESORT` | 1000000 | finite last resort — reachable, but only when nothing else applies |
