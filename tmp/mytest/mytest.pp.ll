; ModuleID = 'mytest.pp.bc'
target datalayout = "e-m:o-p:32:32-f64:32:64-f80:128-n8:16:32-S128"
target triple = "i386-apple-macosx10.14.0"

@llvm.used = appending global [4 x i8*] [i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*), i8* bitcast (void ()* @seahorn.fail to i8*)], section "llvm.metadata"

; Function Attrs: nounwind ssp
define i32 @main() #0 {
  %1 = call i32 @verifier.nondet.1() #2
  %2 = call i32 @verifier.nondet.1() #2
  %3 = call i32 @verifier.nondet.1() #2
  %4 = call i32 @verifier.nondet.1() #2
  %5 = call i32 @verifier.nondet.1() #2
  call void @seahorn.fn.enter() #2
  %6 = icmp sgt i32 %5, 0
  %7 = icmp slt i32 %4, 200
  %or.cond = and i1 %6, %7
  %8 = icmp slt i32 %3, 20
  %or.cond1 = and i1 %or.cond, %8
  br i1 %or.cond1, label %9, label %17

; <label>:9                                       ; preds = %11, %0
  %a.0 = phi i32 [ %12, %11 ], [ %2, %0 ]
  %b.0 = phi i32 [ %13, %11 ], [ %1, %0 ]
  %10 = icmp sgt i32 %b.0, 0
  br i1 %10, label %11, label %14

; <label>:11                                      ; preds = %9
  %12 = add nsw i32 %a.0, 1
  %13 = add nsw i32 %b.0, -1
  br label %9

; <label>:14                                      ; preds = %9
  %15 = icmp sgt i32 %a.0, 0
  br i1 %15, label %17, label %16

; <label>:16                                      ; preds = %14
  call void @verifier.error() #2
  unreachable

; <label>:17                                      ; preds = %14, %0
  ret i32 0
}

declare void @verifier.assume(i1)

declare void @verifier.assume.not(i1)

declare void @seahorn.fail()

; Function Attrs: noreturn
declare void @verifier.error() #1

declare void @seahorn.fn.enter()

declare i32 @verifier.nondet.1()

attributes #0 = { nounwind ssp "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { noreturn }
attributes #2 = { nounwind }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"PIC Level", i32 2}
!1 = !{!"clang version 3.6.0 (tags/RELEASE_360/final)"}