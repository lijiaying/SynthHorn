; ModuleID = 'mytest.bc'
target datalayout = "e-m:o-p:32:32-f64:32:64-f80:128-n8:16:32-S128"
target triple = "i386-apple-macosx10.14.0"

; Function Attrs: nounwind ssp
define i32 @main() #0 {
  %1 = alloca i32, align 4
  %a = alloca i32, align 4
  %b = alloca i32, align 4
  store i32 0, i32* %1
  %2 = load i32* %a, align 4
  %3 = icmp sgt i32 %2, 0
  br i1 %3, label %4, label %24

; <label>:4                                       ; preds = %0
  %5 = load i32* %a, align 4
  %6 = icmp slt i32 %5, 200
  br i1 %6, label %7, label %24

; <label>:7                                       ; preds = %4
  %8 = load i32* %b, align 4
  %9 = icmp slt i32 %8, 20
  br i1 %9, label %10, label %24

; <label>:10                                      ; preds = %7
  br label %11

; <label>:11                                      ; preds = %14, %10
  %12 = load i32* %b, align 4
  %13 = icmp sgt i32 %12, 0
  br i1 %13, label %14, label %19

; <label>:14                                      ; preds = %11
  %15 = load i32* %a, align 4
  %16 = add nsw i32 %15, 1
  store i32 %16, i32* %a, align 4
  %17 = load i32* %b, align 4
  %18 = add nsw i32 %17, -1
  store i32 %18, i32* %b, align 4
  br label %11

; <label>:19                                      ; preds = %11
  %20 = load i32* %a, align 4
  %21 = icmp sgt i32 %20, 0
  br i1 %21, label %23, label %22

; <label>:22                                      ; preds = %19
  call void @__VERIFIER_error()
  br label %23

; <label>:23                                      ; preds = %22, %19
  br label %24

; <label>:24                                      ; preds = %23, %7, %4, %0
  %25 = load i32* %1
  ret i32 %25
}

declare void @__VERIFIER_error() #1

attributes #0 = { nounwind ssp "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"PIC Level", i32 2}
!1 = !{!"clang version 3.6.0 (tags/RELEASE_360/final)"}
