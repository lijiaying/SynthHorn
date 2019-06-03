; ModuleID = 'mytest2.bc'
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
  tail call void @seahorn.fn.enter() #2
  %1 = icmp sgt i32 %0, 2
  tail call void @verifier.assume.not(i1 %1) #2
  %2 = xor i1 %1, true
  tail call void @llvm.assume(i1 %2), !seahorn !2
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
