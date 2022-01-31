
(define-sort env32 () (Array String (_ BitVec 32)))

(declare-const rho env32)
(declare-const rho Bool)
(assert (not (= (select rho "x") (select rho "#0"))))
(assert (= rho true))
(check-sat)
(get-model)