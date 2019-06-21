; ModuleID = 'simple.pp.ms.o.bc'
target datalayout = "e-m:o-p:32:32-f64:32:64-f80:128-n8:16:32-S128"
target triple = "i386-apple-macosx10.14.0"

@llvm.used = appending global [4 x i8*] [i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*), i8* bitcast (void ()* @seahorn.fail to i8*)], section "llvm.metadata"

declare i32 @unknown(...) #0

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
  %0 = tail call i32 bitcast (i32 (...)* @unknown to i32 ()*)() #3
  %.off.i = add i32 %0, -1
  %1 = icmp ult i32 %.off.i, 19
  tail call void @verifier.assume(i1 %1) #3
  tail call void @llvm.assume(i1 %1), !seahorn !2
  %2 = add nsw i32 %0, 2
  %3 = icmp sgt i32 %2, -1
  tail call void @verifier.assume.not(i1 %3) #3
  %4 = xor i1 %3, true
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
