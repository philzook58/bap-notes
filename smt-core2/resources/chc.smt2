(set-logic HORN)
(set-option :produce-proofs true)
(set-option :fp.engine spacer)
;(set-option :fp.bmc.linear_unrolling_depth 10)
;(set-option :fp.generate_proof_trace true)

(include "simple.smt2")

; init
;(assert
;(forall ((LR (_ BitVec 32)) (R0 (_ BitVec 32)))
;  (=> (label #x00000000 LR R0)
;   false)))
(assert
 (forall ((LR (_ BitVec 32)) (R0 (_ BitVec 32)))
  (label #x00000000 LR R0))) ;; all possible initial states
  ;; if inital constaint is constrained
;0x4
(assert
 (forall ((LR (_ BitVec 32)) (R0 (_ BitVec 32)))
  (=> (label #x00000004 LR R0)
   (not (= R0 #x0000000a)))))
;; we are backchaining from bad states
;; label is predicate describing over approximation of state at that address.
;; Maybe I shold call it state. or reachable state.

(check-sat)
(get-proof)
;(get-model)
