; ModuleID = 'test.bc'
target datalayout = "e-m:o-p:32:32-f64:32:64-f80:128-n8:16:32-S128"
target triple = "i386-apple-macosx10.14.0"

@llvm.used = appending global [4 x i8*] [i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*), i8* bitcast (void ()* @seahorn.fail to i8*)], section "llvm.metadata"

declare i32 @unknown1(...) #0

declare void @verifier.assume(i1)

declare void @verifier.assume.not(i1)

declare void @seahorn.fail()

; Function Attrs: noreturn
declare void @verifier.error() #1

declare void @seahorn.fn.enter()

; Function Attrs: nounwind ssp
define i32 @main() #2 {
entry:
  tail call void @seahorn.fn.enter() #3
  br label %0

; <label>:0                                       ; preds = %0, %entry
  %a.0.i = phi i32 [ 7, %entry ], [ %3, %0 ]
  %1 = tail call i32 bitcast (i32 (...)* @unknown1 to i32 ()*)() #3
  %2 = icmp eq i32 %1, 0
  %3 = add i32 %a.0.i, 1
  br i1 %2, label %verifier.error, label %0

verifier.error:                                   ; preds = %0
  %a.0.i.lcssa = phi i32 [ %a.0.i, %0 ]
  %4 = icmp eq i32 %a.0.i.lcssa, 0
  tail call void @verifier.assume(i1 %4) #3
  tail call void @llvm.assume(i1 %4), !seahorn !2
  tail call void @seahorn.fail() #3
  ret i32 42
}

; Function Attrs: nounwind
declare void @llvm.assume(i1) #3

attributes #0 = { "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { noreturn }
attributes #2 = { nounwind ssp "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { nounwind }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"PIC Level", i32 2}
!1 = !{!"clang version 3.6.0 (tags/RELEASE_360/final)"}
!2 = !{}
