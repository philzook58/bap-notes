(set-option :fp.engine bmc)
(declare-rel reach-state ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32)))
(declare-rel init-state ( (_ BitVec 32) (_ BitVec 32)))
(declare-var LR (_ BitVec 32)) (declare-var R0 (_ BitVec 32))
;0x0
(rule
 (=> (reach-state #x00000000 LR R0)
  (let ((R0 (bvadd R0 #x00000001))) (reach-state #x00000004 LR R0))))
;0x4
(rule
 (=> (reach-state #x00000004 LR R0)
   (reach-state #x00000008 LR R0)))

(rule
 (=> (init-state LR R0)
   (reach-state #x00000000 LR R0)))
(rule (init-state LR R0))
;(rule (reach-state #x00000000 LR R0))
(query init-state :print-answer true)
