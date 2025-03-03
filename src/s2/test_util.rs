use rand::Rng;

// random_uniform_int returns a uniformly distributed integer in the range [0,n).
pub fn random_uniform_int(n: u32) -> u32 {
    rand::thread_rng().gen_range(0..n)
}

// random_uniform_float64 returns a uniformly distributed value in the range [min, max).
pub fn random_uniform_float64(min: f64, max: f64) -> f64 {
    min + rand::random::<f64>() * (max - min)
}

// one_in returns true with a probability of 1/n.
pub fn one_in_n(n: u32) -> bool {
    rand::random::<u32>() % n == 0
}
