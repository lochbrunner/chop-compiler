static MIN_DEF: &str = "
; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @min_i32__i32_i32(i32, i32) #0 {
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  store i32 %0, i32* %3, align 4
  store i32 %1, i32* %4, align 4
  %5 = load i32, i32* %3, align 4
  %6 = load i32, i32* %4, align 4
  %7 = icmp slt i32 %5, %6
  br i1 %7, label %8, label %10

; <label>:8:                                      ; preds = %2
  %9 = load i32, i32* %3, align 4
  br label %12

; <label>:10:                                     ; preds = %2
  %11 = load i32, i32* %4, align 4
  br label %12

; <label>:12:                                     ; preds = %10, %8
  %13 = phi i32 [ %9, %8 ], [ %11, %10 ]
  ret i32 %13
}

";

static MAX_DEF: &str = "
; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @max_i32__i32_i32(i32, i32) #0 {
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  store i32 %0, i32* %3, align 4
  store i32 %1, i32* %4, align 4
  %5 = load i32, i32* %3, align 4
  %6 = load i32, i32* %4, align 4
  %7 = icmp sgt i32 %5, %6
  br i1 %7, label %8, label %10

; <label>:8:                                      ; preds = %2
  %9 = load i32, i32* %3, align 4
  br label %12

; <label>:10:                                     ; preds = %2
  %11 = load i32, i32* %4, align 4
  br label %12

; <label>:12:                                     ; preds = %10, %8
  %13 = phi i32 [ %9, %8 ], [ %11, %10 ]
  ret i32 %13
}
";

static MAX_DEF_UC: &str = "; Function Attrs: noinline nounwind optnone uwtable
define dso_local zeroext i8 @max_i8__i8_i8(i8 noundef zeroext %0, i8 noundef zeroext %1) #0 {
  %3 = alloca i8, align 1
  %4 = alloca i8, align 1
  store i8 %0, i8* %3, align 1
  store i8 %1, i8* %4, align 1
  %5 = load i8, i8* %3, align 1
  %6 = zext i8 %5 to i32
  %7 = load i8, i8* %4, align 1
  %8 = zext i8 %7 to i32
  %9 = icmp sgt i32 %6, %8
  br i1 %9, label %10, label %13

10:                                               ; preds = %2
  %11 = load i8, i8* %3, align 1
  %12 = zext i8 %11 to i32
  br label %16

13:                                               ; preds = %2
  %14 = load i8, i8* %4, align 1
  %15 = zext i8 %14 to i32
  br label %16

16:                                               ; preds = %13, %10
  %17 = phi i32 [ %12, %10 ], [ %15, %13 ]
  %18 = trunc i32 %17 to i8
  ret i8 %18
}";

static MIN_DEF_UC: &str = "; Function Attrs: noinline nounwind optnone uwtable
define dso_local zeroext i8 @min_i8__i8_i8(i8 noundef zeroext %0, i8 noundef zeroext %1) #0 {
  %3 = alloca i8, align 1
  %4 = alloca i8, align 1
  store i8 %0, i8* %3, align 1
  store i8 %1, i8* %4, align 1
  %5 = load i8, i8* %3, align 1
  %6 = zext i8 %5 to i32
  %7 = load i8, i8* %4, align 1
  %8 = zext i8 %7 to i32
  %9 = icmp slt i32 %6, %8
  br i1 %9, label %10, label %13

10:                                               ; preds = %2
  %11 = load i8, i8* %3, align 1
  %12 = zext i8 %11 to i32
  br label %16

13:                                               ; preds = %2
  %14 = load i8, i8* %4, align 1
  %15 = zext i8 %14 to i32
  br label %16

16:                                               ; preds = %13, %10
  %17 = phi i32 [ %12, %10 ], [ %15, %13 ]
  %18 = trunc i32 %17 to i8
  ret i8 %18
}";

static MAX_DEF_F: &str = "
; Function Attrs: noinline nounwind optnone uwtable
define dso_local float @max_float__float_float(float noundef %0, float noundef %1) #0 {
  %3 = alloca float, align 4
  %4 = alloca float, align 4
  store float %0, float* %3, align 4
  store float %1, float* %4, align 4
  %5 = load float, float* %3, align 4
  %6 = load float, float* %4, align 4
  %7 = fcmp ogt float %5, %6
  br i1 %7, label %8, label %10

8:                                                ; preds = %2
  %9 = load float, float* %3, align 4
  br label %12

10:                                               ; preds = %2
  %11 = load float, float* %4, align 4
  br label %12

12:                                               ; preds = %10, %8
  %13 = phi float [ %9, %8 ], [ %11, %10 ]
  ret float %13
}
";

static MIN_DEF_F: &str = "
; Function Attrs: noinline nounwind optnone uwtable
define dso_local float @min_float__float_float(float noundef %0, float noundef %1) #0 {
  %3 = alloca float, align 4
  %4 = alloca float, align 4
  store float %0, float* %3, align 4
  store float %1, float* %4, align 4
  %5 = load float, float* %3, align 4
  %6 = load float, float* %4, align 4
  %7 = fcmp olt float %5, %6
  br i1 %7, label %8, label %10

8:                                                ; preds = %2
  %9 = load float, float* %3, align 4
  br label %12

10:                                               ; preds = %2
  %11 = load float, float* %4, align 4
  br label %12

12:                                               ; preds = %10, %8
  %13 = phi float [ %9, %8 ], [ %11, %10 ]
  ret float %13
}
";

static MAX_DEF_D: &str = "
; Function Attrs: noinline nounwind optnone uwtable
define dso_local double @max_double__double_double(double noundef %0, double noundef %1) #0 {
  %3 = alloca double, align 8
  %4 = alloca double, align 8
  store double %0, double* %3, align 8
  store double %1, double* %4, align 8
  %5 = load double, double* %3, align 8
  %6 = load double, double* %4, align 8
  %7 = fcmp ogt double %5, %6
  br i1 %7, label %8, label %10

8:                                                ; preds = %2
  %9 = load double, double* %3, align 8
  br label %12

10:                                               ; preds = %2
  %11 = load double, double* %4, align 8
  br label %12

12:                                               ; preds = %10, %8
  %13 = phi double [ %9, %8 ], [ %11, %10 ]
  ret double %13
}
";
static MIN_DEF_D: &str = "
; Function Attrs: noinline nounwind optnone uwtable
define dso_local double @min_double__double_double(double noundef %0, double noundef %1) #0 {
  %3 = alloca double, align 8
  %4 = alloca double, align 8
  store double %0, double* %3, align 8
  store double %1, double* %4, align 8
  %5 = load double, double* %3, align 8
  %6 = load double, double* %4, align 8
  %7 = fcmp olt double %5, %6
  br i1 %7, label %8, label %10

8:                                                ; preds = %2
  %9 = load double, double* %3, align 8
  br label %12

10:                                               ; preds = %2
  %11 = load double, double* %4, align 8
  br label %12

12:                                               ; preds = %10, %8
  %13 = phi double [ %9, %8 ], [ %11, %10 ]
  ret double %13
}";

pub fn write_functions(code: &mut String) {
    code.push_str(MIN_DEF);
    code.push_str(MAX_DEF);
    code.push_str(MAX_DEF_UC);
    code.push_str(MIN_DEF_UC);
    code.push_str(MAX_DEF_F);
    code.push_str(MIN_DEF_F);
    code.push_str(MAX_DEF_D);
    code.push_str(MIN_DEF_D);
}
