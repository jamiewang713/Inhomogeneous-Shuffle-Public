import Lean
import Mathlib.Tactic
import RiffleLowerV2.Thinning.Compat.FiniteLaw

set_option Elab.async false

open Lean Elab Command in
run_cmd do
  let oldType : Expr :=
    Lean.Expr.forallE
      `Ω
      (Lean.Expr.sort (Lean.Level.succ (Lean.Level.param `u_1)))
      (Lean.Expr.forallE
        (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».FiniteLawTypeBefore 2572071053) "_hygCtx") "_hyg") 3)
        (Lean.Expr.app (Lean.Expr.const `Fintype [Lean.Level.param `u_1]) (Lean.Expr.bvar 0))
        (Lean.Expr.forallE
          `p
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.const `RiffleLowerV2.Thinning.Compat.FiniteLaw [Lean.Level.param `u_1])
              (Lean.Expr.bvar 1))
            (Lean.Expr.bvar 0))
          (Lean.Expr.forallE
            (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».FiniteLawTypeBefore 2572071053) "_hygCtx") "_hyg") 8)
            (Lean.Expr.app (Lean.Expr.const `MeasurableSpace [Lean.Level.param `u_1]) (Lean.Expr.bvar 2))
            (Lean.Expr.forallE
              (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `inst.«_@».FiniteLawTypeBefore 2572071053) "_hygCtx") "_hyg") 11)
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `MeasurableSingletonClass [Lean.Level.param `u_1]) (Lean.Expr.bvar 3))
                (Lean.Expr.bvar 0))
              (Lean.Expr.forallE
                `f
                (Lean.Expr.forallE
              (Lean.Name.mkNum `auditBinder 0)
                  (Lean.Expr.bvar 4)
                  (Lean.Expr.const `Real [])
                  (Lean.BinderInfo.default))
                (Lean.Expr.app
                  (Lean.Expr.app
                    (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Real []))
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `MeasureTheory.integral [Lean.Level.param `u_1, Lean.Level.zero])
                                  (Lean.Expr.bvar 5))
                                (Lean.Expr.const `Real []))
                              (Lean.Expr.const `Real.normedAddCommGroup []))
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.app
                                      (Lean.Expr.const `InnerProductSpace.toNormedSpace [Lean.Level.zero, Lean.Level.zero])
                                      (Lean.Expr.const `Real []))
                                    (Lean.Expr.const `Real []))
                                  (Lean.Expr.const `Real.instRCLike []))
                                (Lean.Expr.app
                                  (Lean.Expr.app
                                    (Lean.Expr.const `NormedAddCommGroup.toSeminormedAddCommGroup [Lean.Level.zero])
                                    (Lean.Expr.const `Real []))
                                  (Lean.Expr.const `Real.normedAddCommGroup [])))
                              (Lean.Expr.app
                                (Lean.Expr.app
                                  (Lean.Expr.const `RCLike.toInnerProductSpaceReal [Lean.Level.zero])
                                  (Lean.Expr.const `Real []))
                                (Lean.Expr.const `Real.instRCLike []))))
                          (Lean.Expr.bvar 2))
                        (Lean.Expr.app
                          (Lean.Expr.app
                            (Lean.Expr.app (Lean.Expr.const `PMF.toMeasure [Lean.Level.param `u_1]) (Lean.Expr.bvar 5))
                            (Lean.Expr.bvar 2))
                          (Lean.Expr.app
                            (Lean.Expr.app
                              (Lean.Expr.app
                                (Lean.Expr.const `RiffleLowerV2.Thinning.Compat.FiniteLaw.toPMF [Lean.Level.param `u_1])
                                (Lean.Expr.bvar 5))
                              (Lean.Expr.bvar 4))
                            (Lean.Expr.bvar 3))))
                      (Lean.Expr.lam
                        `ω
                        (Lean.Expr.bvar 5)
                        (Lean.Expr.app (Lean.Expr.bvar 1) (Lean.Expr.bvar 0))
                        (Lean.BinderInfo.default))))
                  (Lean.Expr.app
                    (Lean.Expr.app
                      (Lean.Expr.app
                        (Lean.Expr.app
                          (Lean.Expr.const `RiffleLowerV2.Thinning.Compat.FiniteLaw.expect [Lean.Level.param `u_1])
                          (Lean.Expr.bvar 5))
                        (Lean.Expr.bvar 4))
                      (Lean.Expr.bvar 3))
                    (Lean.Expr.bvar 0)))
                (Lean.BinderInfo.default))
              (Lean.BinderInfo.instImplicit))
            (Lean.BinderInfo.instImplicit))
          (Lean.BinderInfo.default))
        (Lean.BinderInfo.instImplicit))
      (Lean.BinderInfo.implicit)
  let current ← getConstInfo `RiffleLowerV2.Thinning.Compat.FiniteLaw.integral_toPMF
  unless hash oldType == 2960618758 && hash current.type == 9792095 do
    throwError "Unexpected input type fingerprints"
  liftCoreM <| addDecl (.thmDecl {
    name := `ElaborationAudit.integral_toPMF_original_type
    levelParams := current.levelParams
    type := oldType
    value := mkConst current.name (current.levelParams.map Level.param)
  })
  logInfo "INTEGRAL_ORIGINAL_TYPE_KERNEL_CHECK_OK"
