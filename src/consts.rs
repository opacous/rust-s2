/// Define the maximum rounding error for arithmetic operations. Depending on the
/// platform the mantissa precision may be different than others, so we choose to
/// use specific values to be consistent across all.
/// The values come from the C++ implementation.

/// EPSILON is a small number that represents a reasonable level of noise between two
/// values that can be considered to be equal.
pub const EPSILON: f64 = 1e-14;

/// DBL_EPSILON is a smaller number for values that require more precision.
pub const DBL_EPSILON: f64 = 2.220446049250313e-16;

#[macro_export]
macro_rules! f64_eq {
    ($x:expr, $y:expr) => {
        ($x - $y).abs() < EPSILON
    };
}

#[macro_export]
macro_rules! assert_f64_eq {
    // Basic version with default epsilon
    ($x:expr, $y:expr) => {
        assert_f64_eq!($x, $y, EPSILON, "assertion failed");
    };

    // With custom epsilon
    ($x:expr, $y:expr, $epsilon:expr) => {
        assert_f64_eq!($x, $y, $epsilon, "assertion failed");
    };

    // With custom epsilon and error message
    ($x:expr, $y:expr, $epsilon:expr, $msg:expr) => {
        let x_val = $x;
        let y_val = $y;
        let diff = (x_val - y_val).abs();
        if diff >= $epsilon {
            panic!(
                concat!(
                    "{}\n",
                    "Expected: {}\n",
                    "Actual:   {}\n",
                    "Diff:     {}\n",
                    "Epsilon:  {}\n",
                    "Ratio:    {:.2}x larger than epsilon"
                ),
                $msg,
                x_val,
                y_val,
                diff,
                $epsilon,
                diff / $epsilon
            );
        }
    };

    // With custom error message (uses default epsilon)
    ($x:expr, $y:expr, $msg:expr) => {
        assert_f64_eq!($x, $y, EPSILON, $msg);
    };
}

#[allow(unused)]
/// f64_eq reports whether the two values are within the default epsilon.
pub fn f64_eq(x: f64, y: f64) -> bool {
    f64_near(x, y, EPSILON)
}

#[allow(unused)]
/// f64_near reports whether the two values are within the specified epsilon.
pub fn f64_near(x: f64, y: f64, eps: f64) -> bool {
    (x - y).abs() <= eps
}

///TODO: to util module?
pub fn remainder(x: f64, y: f64) -> f64 {
    ::libm::remquo(x, y).0
}

pub fn clamp<T>(val: T, min: T, max: T) -> T
where
    T: PartialOrd,
{
    if val < min {
        min
    } else if val > max {
        max
    } else {
        val
    }
}

pub fn search_lower_by<F>(len: usize, f: F) -> usize
where
    F: Fn(usize) -> bool,
{
    let mut i = 0;
    let mut j = len;

    while i < j {
        let h = i + (j - i) / 2;
        if !f(h) {
            i = h + 1;
        } else {
            j = h;
        }
    }
    i
}
