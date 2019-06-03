; ModuleID = '04.bc'
target datalayout = "e-m:o-p:32:32-f64:32:64-f80:128-n8:16:32-S128"
target triple = "i386-apple-macosx10.14.0"

@llvm.used = appending global [4 x i8*] [i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*), i8* bitcast (void ()* @seahorn.fail to i8*)], section "llvm.metadata"

; Function Attrs: nounwind ssp
define internal fastcc i32 @fibo(i32 %n) #0 {
  tail call void @seahorn.fn.enter() #2
  %1 = icmp slt i32 %n, 1
  br i1 %1, label %10, label %2

; <label>:2                                       ; preds = %0
  %3 = icmp eq i32 %n, 1
  br i1 %3, label %10, label %4

; <label>:4                                       ; preds = %2
  %5 = add nsw i32 %n, -1
  %6 = tail call fastcc i32 @fibo(i32 %5)
  %7 = add nsw i32 %n, -2
  %8 = tail call fastcc i32 @fibo(i32 %7)
  %9 = add nsw i32 %8, %6
  ret i32 %9

; <label>:10                                      ; preds = %2, %0
  %.0 = phi i32 [ 0, %0 ], [ 1, %2 ]
  ret i32 %.0
}

declare void @verifier.assume(i1)

declare void @verifier.assume.not(i1)

declare void @seahorn.fail()

; Function Attrs: noreturn
declare void @verifier.error() #1

declare void @seahorn.fn.enter()

; Function Attrs: nounwind ssp
define i32 @main() #0 {
entry:
  tail call void @seahorn.fn.enter() #2
  %0 = tail call fastcc i32 @fibo(i32 10) #2
  %1 = icmp eq i32 %0, 55
  tail call void @verifier.assume.not(i1 %1) #2
  %2 = xor i1 %1, true
  tail call void @llvm.assume(i1 %2), !seahorn !2
  tail call void @seahorn.fail() #2
  ret i32 42
}

; Function Attrs: nounwind
declare void @llvm.assume(i1) #2

attributes #0 = { nounwind ssp "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { noreturn }
attributes #2 = { nounwind }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"PIC Level", i32 2}
!1 = !{!"clang version 3.6.0 (tags/RELEASE_360/final)"}
!2 = !{}
