; ModuleID = 'mytest.pp.ms.o.bc'
target datalayout = "e-m:o-p:32:32-f64:32:64-f80:128-n8:16:32-S128"
target triple = "i386-apple-macosx10.14.0"

@llvm.used = appending global [4 x i8*] [i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*), i8* bitcast (void ()* @seahorn.fail to i8*)], section "llvm.metadata"

declare void @verifier.assume(i1)

declare void @verifier.assume.not(i1)

declare void @seahorn.fail()

; Function Attrs: noreturn
declare void @verifier.error() #0

declare void @seahorn.fn.enter()

declare i32 @verifier.nondet.1()

; Function Attrs: nounwind ssp
define i32 @main() #1 {
entry:
  %0 = tail call i32 @verifier.nondet.1() #2
  %1 = tail call i32 @verifier.nondet.1() #2
  %2 = tail call i32 @verifier.nondet.1() #2
  %3 = tail call i32 @verifier.nondet.1() #2
  %4 = tail call i32 @verifier.nondet.1() #2
  tail call void @seahorn.fn.enter() #2
  %5 = icmp sgt i32 %4, 0
  %6 = icmp slt i32 %3, 200
  %or.cond.i = and i1 %6, %5
  %7 = icmp slt i32 %2, 20
  %or.cond1.i = and i1 %7, %or.cond.i
  tail call void @verifier.assume(i1 %or.cond1.i) #2
  tail call void @llvm.assume(i1 %5)
  tail call void @llvm.assume(i1 %6)
  tail call void @llvm.assume(i1 %7)
  %8 = icmp sgt i32 %0, 0
  br i1 %8, label %.lr.ph.preheader, label %verifier.error

.lr.ph.preheader:                                 ; preds = %entry
  br label %.lr.ph

.lr.ph:                                           ; preds = %.lr.ph, %.lr.ph.preheader
  %b.0.i2 = phi i32 [ %10, %.lr.ph ], [ %0, %.lr.ph.preheader ]
  %a.0.i1 = phi i32 [ %9, %.lr.ph ], [ %1, %.lr.ph.preheader ]
  %9 = add nsw i32 %a.0.i1, 1
  %10 = add nsw i32 %b.0.i2, -1
  %11 = icmp sgt i32 %b.0.i2, 1
  br i1 %11, label %.lr.ph, label %verifier.error.loopexit

verifier.error.loopexit:                          ; preds = %.lr.ph
  %.lcssa = phi i32 [ %9, %.lr.ph ]
  br label %verifier.error

verifier.error:                                   ; preds = %verifier.error.loopexit, %entry
  %a.0.i.lcssa = phi i32 [ %1, %entry ], [ %.lcssa, %verifier.error.loopexit ]
  %12 = icmp sgt i32 %a.0.i.lcssa, 0
  tail call void @verifier.assume.not(i1 %12) #2
  %13 = xor i1 %12, true
  tail call void @llvm.assume(i1 %13), !seahorn !2
  tail call void @seahorn.fail() #2
  ret i32 42
}

; Function Attrs: nounwind
declare void @llvm.assume(i1) #2

attributes #0 = { noreturn }
attributes #1 = { nounwind ssp "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { nounwind }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"PIC Level", i32 2}
!1 = !{!"clang version 3.6.0 (tags/RELEASE_360/final)"}
!2 = !{}
