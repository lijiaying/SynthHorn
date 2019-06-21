; ModuleID = 'simple.pp.bc'
target datalayout = "e-m:o-p:32:32-f64:32:64-f80:128-n8:16:32-S128"
target triple = "i386-apple-macosx10.14.0"

@llvm.used = appending global [4 x i8*] [i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*), i8* bitcast (void ()* @seahorn.fail to i8*)], section "llvm.metadata"

; Function Attrs: nounwind ssp
define i32 @main() #0 {
  call void @seahorn.fn.enter() #3
  %1 = call i32 bitcast (i32 (...)* @unknown to i32 ()*)() #3
  %.off = add i32 %1, -1
  %2 = icmp ult i32 %.off, 19
  br i1 %2, label %3, label %11

; <label>:3                                       ; preds = %5, %0
  %a.0 = phi i32 [ %6, %5 ], [ %1, %0 ]
  %b.0 = phi i32 [ %7, %5 ], [ 3, %0 ]
  %4 = icmp sgt i32 %b.0, 0
  br i1 %4, label %5, label %8

; <label>:5                                       ; preds = %3
  %6 = add nsw i32 %a.0, 1
  %7 = add nsw i32 %b.0, -1
  br label %3

; <label>:8                                       ; preds = %3
  %9 = icmp sgt i32 %a.0, 0
  br i1 %9, label %11, label %10

; <label>:10                                      ; preds = %8
  call void @verifier.error() #3
  unreachable

; <label>:11                                      ; preds = %8, %0
  ret i32 0
}

declare i32 @unknown(...) #1

declare void @verifier.assume(i1)

declare void @verifier.assume.not(i1)

declare void @seahorn.fail()

; Function Attrs: noreturn
declare void @verifier.error() #2

declare void @seahorn.fn.enter()

attributes #0 = { nounwind ssp "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { noreturn }
attributes #3 = { nounwind }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"PIC Level", i32 2}
!1 = !{!"clang version 3.6.0 (tags/RELEASE_360/final)"}
