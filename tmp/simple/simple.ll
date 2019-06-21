; ModuleID = 'simple.bc'
target datalayout = "e-m:o-p:32:32-f64:32:64-f80:128-n8:16:32-S128"
target triple = "i386-apple-macosx10.14.0"

; Function Attrs: nounwind ssp
define i32 @main() #0 {
  %1 = alloca i32, align 4
  %a = alloca i32, align 4
  %b = alloca i32, align 4
  store i32 0, i32* %1
  store i32 3, i32* %b, align 4
  %2 = load i32* %a, align 4
  %3 = icmp sgt i32 %2, 0
  br i1 %3, label %4, label %21

; <label>:4                                       ; preds = %0
  %5 = load i32* %a, align 4
  %6 = icmp slt i32 %5, 20
  br i1 %6, label %7, label %21

; <label>:7                                       ; preds = %4
  br label %8

; <label>:8                                       ; preds = %11, %7
  %9 = load i32* %b, align 4
  %10 = icmp sgt i32 %9, 0
  br i1 %10, label %11, label %16

; <label>:11                                      ; preds = %8
  %12 = load i32* %a, align 4
  %13 = add nsw i32 %12, 1
  store i32 %13, i32* %a, align 4
  %14 = load i32* %b, align 4
  %15 = add nsw i32 %14, -1
  store i32 %15, i32* %b, align 4
  br label %8

; <label>:16                                      ; preds = %8
  %17 = load i32* %a, align 4
  %18 = icmp sgt i32 %17, 0
  br i1 %18, label %20, label %19

; <label>:19                                      ; preds = %16
  call void @__VERIFIER_error()
  br label %20

; <label>:20                                      ; preds = %19, %16
  br label %21

; <label>:21                                      ; preds = %20, %4, %0
  %22 = load i32* %1
  ret i32 %22
}

declare void @__VERIFIER_error() #1

attributes #0 = { nounwind ssp "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"PIC Level", i32 2}
!1 = !{!"clang version 3.6.0 (tags/RELEASE_360/final)"}
