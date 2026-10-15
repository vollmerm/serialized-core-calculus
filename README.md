# serialized-calc-redex

A PLT Redex model of a small calculus for functional programs over
contiguous serialized data. Programs read and write values in place through
cursors: readers are affine, writers are linear.

## Running

Needs Racket with the `redex` package (included in the full distribution).

```sh
raco test *.rkt     # type checking, the machine, and sampled metatheory
racket demo.rkt     # step logs for the worked examples
```

## Modules

| module | contents |
| --- | --- |
| `shape.rkt` | shapes, values, cells |
| `layout.rkt` | the encoding, as a relation in both directions |
| `protocol.rkt` | protocol rows |
| `capability.rkt` | readers, writers, canonical forms |
| `syntax.rkt` | terms, types, signatures |
| `match.rkt` | solving a signature's protocol tails at a call site |
| `typing.rkt` | the typing judgment |
| `machine.rkt` | configurations and the step relation |
| `examples.rkt` | worked programs |
| `properties.rkt` | metatheory, checked on sampled inputs |
| `explore.rkt` | step logs, reduction graphs, typing derivations |
| `demo.rkt` | entry points onto the examples |
| `span-candidate.rkt` | an alternative design using spans |

## Examples

Type checking:

```racket
> (require redex/reduction-semantics "examples.rkt" "typing.rkt" "machine.rkt" "explore.rkt")
> build-seven
'(let (bind () (w)) (new Int) (let (bind () (w2)) (write-int w 7) (finish w2)))
> (type-of (term ()) build-seven)
'((bundle ((Ser Int)) ()))
```

Running:

```racket
> (result-of (run-term (term ()) build-seven))
'(ser Int ((I 7)))
> sample-tree
'(inr ((inl (1)) (inr ((inl (2)) (inl (3))))))
> (result-of (run-term recursive-signatures (sum-tree-program sample-tree)))
6
> (result-of (run-term recursive-signatures (add1-tree-program sample-tree)))
'(ser (Data X (Int) (X X)) (R L (I 2) R L (I 3) L (I 4)))
> (result-of (run-term recursive-signatures (mirror-tree-program sample-tree)))
'(ser (Data X (Int) (X X)) (R R L (I 3) L (I 2) L (I 1)))
```

A program that drops a writer does not type check, and the machine gets
stuck on it:

```racket
> (define drop (term (let (bind () (w)) (new Int) (return (1) ()))))
> (type-of (term ()) drop)
'()
> (run-log (term ()) drop)
0    let            new            ()                                 (1 : (let w))
1    new            (bundle () ((writer 0 cells owing 1))) ()         (1 : (let w))
2    let-continue   return         ((w (writer 0 cells owing 1)))     (1 : (scope w))
3    return         (bundle (1) ()) ((w (writer 0 cells owing 1)))     (1 : (scope w))
4    STUCK
```

In DrRacket, `trace-program` draws the reduction graph, `step-program` opens
a stepper, and `show-typing` draws a typing derivation:

```racket
> (trace-program recursive-signatures (sum-tree-program (leaf 4)))
> (show-typing (term ()) build-seven)
```
