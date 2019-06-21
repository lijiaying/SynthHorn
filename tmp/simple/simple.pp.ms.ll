; ModuleID = 'simple.pp.ms.bc'
target datalayout = "e-m:o-p:32:32-f64:32:64-f80:128-n8:16:32-S128"
target triple = "i386-apple-macosx10.14.0"

@llvm.used = appending global [8 x i8*] [i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*), i8* bitcast (void ()* @seahorn.fail to i8*), i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*), i8* bitcast (void ()* @seahorn.fail to i8*)], section "llvm.metadata"

; Function Attrs: nounwind ssp
define private i32 @orig.main() #0 {
  %1 = call i32 @verifier.nondet.1() #2
  %2 = call i32 @verifier.nondet.1() #2
  %3 = call i32 @verifier.nondet.1() #2
  call void @seahorn.fn.enter() #2
  %4 = icmp sgt i32 %3, 0
  %5 = icmp slt i32 %2, 20
  %or.cond = and i1 %4, %5
  br i1 %or.cond, label %6, label %14

; <label>:6                                       ; preds = %8, %0
  %a.0 = phi i32 [ %9, %8 ], [ %1, %0 ]
  %b.0 = phi i32 [ %10, %8 ], [ 3, %0 ]
  %7 = icmp sgt i32 %b.0, 0
  br i1 %7, label %8, label %11

; <label>:8                                       ; preds = %6
  %9 = add nsw i32 %a.0, 1
  %10 = add nsw i32 %b.0, -1
  br label %6

; <label>:11                                      ; preds = %6
  %12 = icmp sgt i32 %a.0, 0
  br i1 %12, label %14, label %13

; <label>:13                                      ; preds = %11
  call void @verifier.error() #2
  unreachable

; <label>:14                                      ; preds = %11, %0
  ret i32 0
}

declare void @verifier.assume(i1)

declare void @verifier.assume.not(i1)

declare void @seahorn.fail()

; Function Attrs: noreturn
declare void @verifier.error() #1

declare void @seahorn.fn.enter()

declare i32 @verifier.nondet.1()

declare void @verifier.assert(i1)

; Function Attrs: nounwind ssp
define i32 @main() #0 {
entry:
  %0 = call i32 @verifier.nondet.1() #2
  %1 = call i32 @verifier.nondet.1() #2
  %2 = call i32 @verifier.nondet.1() #2
  call void @seahorn.fn.enter() #2
  %3 = icmp sgt i32 %2, 0
  %4 = icmp slt i32 %1, 20
  %or.cond.i = and i1 %3, %4
  call void @verifier.assume(i1 %or.cond.i)
  call void @llvm.assume(i1 %or.cond.i), !seahorn !2
  br label %5

; <label>:5                                       ; preds = %7, %entry
  %a.0.i = phi i32 [ %8, %7 ], [ %0, %entry ]
  %b.0.i = phi i32 [ %9, %7 ], [ 3, %entry ]
  %6 = icmp sgt i32 %b.0.i, 0
  br i1 %6, label %7, label %10

; <label>:7                                       ; preds = %5
  %8 = add nsw i32 %a.0.i, 1
  %9 = add nsw i32 %b.0.i, -1
  br label %5

; <label>:10                                      ; preds = %5
  %11 = icmp sgt i32 %a.0.i, 0
  call void @verifier.assume.not(i1 %11)
  %12 = xor i1 %11, true
  call void @llvm.assume(i1 %12), !seahorn !2
  br label %13

; <label>:13                                      ; preds = %10
  br label %verifier.error

verifier.error:                                   ; preds = %13
  call void @seahorn.fail()
  ret i32 42
}

declare i1 @nondet.bool()

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
