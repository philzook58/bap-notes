(include "prelude.smt2")

(assert
  (exists
    ((rho_temp_Bool (Array String Bool))
     (rho_temp_32 (Array String (_ BitVec 32))))
    (and
     (let
      ((rho_new_Bool rho_temp_Bool) (rho_new_32 rho_temp_32))
      (=
       rho_new_Bool
       (store
        rho_Bool
        "#0"
        (and
         (bvule (select rho_32 "x") #x00000003)
         (not (bvule #x00000003 (select rho_32 "x")))
         true))))
     (let
      ((rho_Bool rho_temp_Bool) (rho_32 rho_temp_32))
      (if
       (select rho_Bool "#0")
       (= rho_new_32 (store rho_32 "x" (select rho_32 "y")))
       (=
        rho_new_32
        (store rho_32 "x" (bvadd (select rho_32 "y") #x00000001))))))))

(assert (bvugt (select rho_new_32 "x") (select rho_new_32 "y")))
(check-sat)
(get-model)
; swap store arguments
; print bitvectors correctly
; bvule produce 1 bit vectors?