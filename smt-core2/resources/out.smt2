(declare-fun label ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 1)
                    (_ BitVec 32) (_ BitVec 1) (_ BitVec 32) (_ BitVec 32)
                    (_ BitVec 1) (_ BitVec 1)) Bool)
(declare-const %P12582905 (_ BitVec 32))
(declare-const %P12582910 (_ BitVec 32)) (declare-const CF (_ BitVec 1))
(declare-const LR (_ BitVec 32)) (declare-const NF (_ BitVec 1))
(declare-const R0 (_ BitVec 32)) (declare-const R3 (_ BitVec 32))
(declare-const VF (_ BitVec 1)) (declare-const ZF (_ BitVec 1))
;0x0
(assert
 (forall
  ((%P12582905 (_ BitVec 32)) (%P12582910 (_ BitVec 32)) (CF (_ BitVec 1))
   (LR (_ BitVec 32)) (NF (_ BitVec 1)) (R0 (_ BitVec 32)) (R3 (_ BitVec 32))
   (VF (_ BitVec 1)) (ZF (_ BitVec 1)))
  (=> (label #x00000000 %P12582905 %P12582910 CF LR NF R0 R3 VF ZF)
   (let ((%P12582910 R0))
    (let ((R3 R0))
     (let ((CF (ite (bvule #x00000000 %P12582910) #b1 #b0)))
      (let
       ((VF
         ((_ extract 0 0)
          (concat #b0000000000000000000000000000000
           (ite (= #b0 #b1)
            (bvlshr (bvand %P12582910 (bvxor %P12582910 R3)) #x0000001f)
            (bvlshr (bvand %P12582910 (bvxor %P12582910 R3)) #x0000001f))))))
       (let
        ((NF
          ((_ extract 0 0)
           (concat #b0000000000000000000000000000000
            (ite (= #b0 #b1) (bvlshr R3 #x0000001f) (bvlshr R3 #x0000001f))))))
        (let
         ((ZF
           (bvand (ite (bvule R3 #x00000000) #b1 #b0)
            (ite (bvule #x00000000 R3) #b1 #b0))))
         (label #x00000004 %P12582905 %P12582910 CF LR NF R0 R3 VF ZF))))))))))
;0x4
(assert
 (forall
  ((%P12582905 (_ BitVec 32)) (%P12582910 (_ BitVec 32)) (CF (_ BitVec 1))
   (LR (_ BitVec 32)) (NF (_ BitVec 1)) (R0 (_ BitVec 32)) (R3 (_ BitVec 32))
   (VF (_ BitVec 1)) (ZF (_ BitVec 1)))
  (=> (label #x00000004 %P12582905 %P12582910 CF LR NF R0 R3 VF ZF)
   (ite
    (=
     (bvor (bvand (ite (bvule ZF #b1) #b1 #b0) (ite (bvule #b1 ZF) #b1 #b0))
      (bvnot (bvand (ite (bvule NF VF) #b1 #b0) (ite (bvule VF NF) #b1 #b0))))
     #b1)
    (label #x0000001c %P12582905 %P12582910 CF LR NF R0 R3 VF ZF)
    (label #x00000008 %P12582905 %P12582910 CF LR NF R0 R3 VF ZF)))))
;0x1c
(assert
 (forall
  ((%P12582905 (_ BitVec 32)) (%P12582910 (_ BitVec 32)) (CF (_ BitVec 1))
   (LR (_ BitVec 32)) (NF (_ BitVec 1)) (R0 (_ BitVec 32)) (R3 (_ BitVec 32))
   (VF (_ BitVec 1)) (ZF (_ BitVec 1)))
  (=> (label #x0000001c %P12582905 %P12582910 CF LR NF R0 R3 VF ZF)
   (let ((R0 #x00000001))
    (label #x00000020 %P12582905 %P12582910 CF LR NF R0 R3 VF ZF)))))
;0x20
(assert
 (forall
  ((%P12582905 (_ BitVec 32)) (%P12582910 (_ BitVec 32)) (CF (_ BitVec 1))
   (LR (_ BitVec 32)) (NF (_ BitVec 1)) (R0 (_ BitVec 32)) (R3 (_ BitVec 32))
   (VF (_ BitVec 1)) (ZF (_ BitVec 1)))
  (=> (label #x00000020 %P12582905 %P12582910 CF LR NF R0 R3 VF ZF)
   (and (label LR %P12582905 %P12582910 CF LR NF R0 R3 VF ZF)
    (label #x00000024 %P12582905 %P12582910 CF LR NF R0 R3 VF ZF)))))
;0x8
(assert
 (forall
  ((%P12582905 (_ BitVec 32)) (%P12582910 (_ BitVec 32)) (CF (_ BitVec 1))
   (LR (_ BitVec 32)) (NF (_ BitVec 1)) (R0 (_ BitVec 32)) (R3 (_ BitVec 32))
   (VF (_ BitVec 1)) (ZF (_ BitVec 1)))
  (=> (label #x00000008 %P12582905 %P12582910 CF LR NF R0 R3 VF ZF)
   (let ((R0 #x00000001))
    (label #x0000000c %P12582905 %P12582910 CF LR NF R0 R3 VF ZF)))))
;0xc
(assert
 (forall
  ((%P12582905 (_ BitVec 32)) (%P12582910 (_ BitVec 32)) (CF (_ BitVec 1))
   (LR (_ BitVec 32)) (NF (_ BitVec 1)) (R0 (_ BitVec 32)) (R3 (_ BitVec 32))
   (VF (_ BitVec 1)) (ZF (_ BitVec 1)))
  (=> (label #x0000000c %P12582905 %P12582910 CF LR NF R0 R3 VF ZF)
   (let ((R0 (bvmul R3 R0)))
    (label #x00000010 %P12582905 %P12582910 CF LR NF R0 R3 VF ZF)))))
;0x10
(assert
 (forall
  ((%P12582905 (_ BitVec 32)) (%P12582910 (_ BitVec 32)) (CF (_ BitVec 1))
   (LR (_ BitVec 32)) (NF (_ BitVec 1)) (R0 (_ BitVec 32)) (R3 (_ BitVec 32))
   (VF (_ BitVec 1)) (ZF (_ BitVec 1)))
  (=> (label #x00000010 %P12582905 %P12582910 CF LR NF R0 R3 VF ZF)
   (let ((%P12582905 R3))
    (let ((R3 (bvsub R3 #x00000001)))
     (let ((CF (ite (bvule #x00000001 %P12582905) #b1 #b0)))
      (let
       ((VF
         ((_ extract 0 0)
          (concat #b0000000000000000000000000000000
           (ite (= #b0 #b1)
            (bvlshr
             (bvand (bvxor %P12582905 #x00000001) (bvxor %P12582905 R3))
             #x0000001f)
            (bvlshr
             (bvand (bvxor %P12582905 #x00000001) (bvxor %P12582905 R3))
             #x0000001f))))))
       (let
        ((NF
          ((_ extract 0 0)
           (concat #b0000000000000000000000000000000
            (ite (= #b0 #b1) (bvlshr R3 #x0000001f) (bvlshr R3 #x0000001f))))))
        (let
         ((ZF
           (bvand (ite (bvule R3 #x00000000) #b1 #b0)
            (ite (bvule #x00000000 R3) #b1 #b0))))
         (label #x00000014 %P12582905 %P12582910 CF LR NF R0 R3 VF ZF))))))))))
;0x14
(assert
 (forall
  ((%P12582905 (_ BitVec 32)) (%P12582910 (_ BitVec 32)) (CF (_ BitVec 1))
   (LR (_ BitVec 32)) (NF (_ BitVec 1)) (R0 (_ BitVec 32)) (R3 (_ BitVec 32))
   (VF (_ BitVec 1)) (ZF (_ BitVec 1)))
  (=> (label #x00000014 %P12582905 %P12582910 CF LR NF R0 R3 VF ZF)
   (ite
    (= (bvand (ite (bvule ZF #b0) #b1 #b0) (ite (bvule #b0 ZF) #b1 #b0)) #b1)
    (label #x0000000c %P12582905 %P12582910 CF LR NF R0 R3 VF ZF)
    (label #x00000018 %P12582905 %P12582910 CF LR NF R0 R3 VF ZF)))))
;0x18
(assert
 (forall
  ((%P12582905 (_ BitVec 32)) (%P12582910 (_ BitVec 32)) (CF (_ BitVec 1))
   (LR (_ BitVec 32)) (NF (_ BitVec 1)) (R0 (_ BitVec 32)) (R3 (_ BitVec 32))
   (VF (_ BitVec 1)) (ZF (_ BitVec 1)))
  (=> (label #x00000018 %P12582905 %P12582910 CF LR NF R0 R3 VF ZF)
   (and (label LR %P12582905 %P12582910 CF LR NF R0 R3 VF ZF)
    (label #x0000001c %P12582905 %P12582910 CF LR NF R0 R3 VF ZF)))))
