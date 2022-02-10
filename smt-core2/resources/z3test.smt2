(declare-const x (_ BitVec 12))
(declare-const y (_ BitVec 4))

(assert (= x (concat #xF #xF y)))
(check-sat)
(get-model)