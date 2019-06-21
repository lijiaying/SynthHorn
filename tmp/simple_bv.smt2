(set-info :original "mytest2.bc")
(set-info :authors "SeaHorn v.0.1.0-rc3")
(define-sort ProgramInt () (_ BitVec 32))

(declare-rel main@entry ())
(declare-rel main@entry.split ())

(declare-var @llvm.used_0 ProgramInt )
(declare-var main@%_0_0 ProgramInt )
(declare-var main@%_1_0 Bool )
(declare-var main@%_2_0 Bool )

(rule main@entry)
(rule (=> (and main@entry
         true
         (bvugt @llvm.used_0 #x00000000)
         (= main@%_1_0 (bvsgt main@%_0_0 #x00000002))
         (not main@%_1_0)
         (= main@%_2_0 (xor main@%_1_0 true)))
    main@entry.split))
(query main@entry.split)

