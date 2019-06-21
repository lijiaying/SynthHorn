; ModuleID = 'simple.bc'
target datalayout = "e-m:o-p:32:32-f64:32:64-f80:128-n8:16:32-S128"
target triple = "i386-apple-macosx10.14.0"

; Function Attrs: nounwind ssp
define i32 @main() #0 {
  %1 = alloca i32, align 4
  %a = alloca i32, align 4
  %b = alloca i32, align 4
  store i32 0, i32* %1
  %2 = call i32 bitcast (i32 (...)* @unknown to i32 ()*)()
  store i32 %2, i32* %a, align 4
  store i32 3, i32* %b, align 4
  %3 = load i32* %a, align 4
  %4 = icmp sgt i32 %3, 0
  br i1 %4, label %5, label %22

; <label>:5                                       ; preds = %0
  %6 = load i32* %a, align 4
  %7 = icmp slt i32 %6, 20
  br i1 %7, label %8, label %22

; <label>:8                                       ; preds = %5
  br label %9

; <label>:9                                       ; preds = %12, %8
  %10 = load i32* %b, align 4
  %11 = icmp sgt i32 %10, 0
  br i1 %11, label %12, label %17

; <label>:12                                      ; preds = %9
  %13 = load i32* %a, align 4
  %14 = add nsw i32 %13, 1
  store i32 %14, i32* %a, align 4
  %15 = load i32* %b, align 4
  %16 = add nsw i32 %15, -1
  store i32 %16, i32* %b, align 4
  br label %9

; <label>:17                                      ; preds = %9
  %18 = load i32* %a, align 4
  %19 = icmp sgt i32 %18, 0
  br i1 %19, label %21, label %20

; <label>:20                                      ; preds = %17
  call void @__VERIFIER_error()
  br label %21

; <label>:21                                      ; preds = %20, %17
  br label %22

; <label>:22                                      ; preds = %21, %5, %0
  %23 = load i32* %1
  ret i32 %23
}

declare i32 @unknown(...) #1

declare void @__VERIFIER_error() #1

attributes #0 = { nounwind ssp "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"PIC Level", i32 2}
!1 = !{!"clang version 3.6.0 (tags/RELEASE_360/final)"}
