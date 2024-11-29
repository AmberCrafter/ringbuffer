#[cfg(feature = "no_std")]
use core::error::Error;
#[cfg(not(feature = "no_std"))]
use std::error::Error;

#[cfg(feature = "no_std")]
use core::fmt::{self, Debug, Display};
#[cfg(not(feature = "no_std"))]
use std::fmt::{self, Debug, Display};

#[cfg(feature = "no_std")]
extern crate alloc;
#[cfg(feature = "no_std")]
use alloc::vec::Vec;

/// `RingBuffer` is a constain space data structure, which maintain itself by indies of head and tail.
///
/// # Example:
///
/// ```
/// use ring_buffer::RingBuffer;
///
/// fn ring_value() {
///     let size = 10;
///     let mut ring = RingBuffer::init(size);
///
///     ring.push(1);
///     assert_eq!(Some(1), ring.pop());
/// }
///
/// fn ring_vector() {
///     let size = 10;
///     let mut ring = RingBuffer::init(size);
///     
///     let data = vec![1,2,3];
///     ring.pushv(data);
///
///     assert_eq!(Some(vec![1,2]), ring.popv(2));
/// }
///
/// fn main() {
///     ring_value();
///     ring_vector();
/// }
/// ```
pub struct RingBuffer<T> {
    head: usize,
    tail: usize,
    size: usize,
    buf: Vec<Option<T>>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum RingBufferError {
    RingBufferFull,
}

impl Display for RingBufferError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl Error for RingBufferError {}
// type BoxError = Box<dyn Error>;
#[cfg(feature = "no_std")]
type Result<T, E = RingBufferError> = core::result::Result<T, E>;
#[cfg(not(feature = "no_std"))]
type Result<T, E = RingBufferError> = std::result::Result<T, E>;

impl<T> RingBuffer<T> {
    pub fn init(size: usize) -> Self {
        RingBuffer {
            head: 0,
            tail: 0,
            size,
            buf: (0..size).map(|_| None).collect(),
        }
    }

    pub fn init_with_vec(buf: Vec<Option<T>>) -> Self {
        RingBuffer {
            head: 0,
            tail: 0,
            size: buf.len(),
            buf,
        }
    }

    pub fn init_with_box(buf: Box<[Option<T>]>) -> Self {
        RingBuffer {
            head: 0,
            tail: 0,
            size: buf.len(),
            buf: buf.into_vec(),
        }
    }

    pub fn is_full(&self) -> bool {
        (self.head) == (self.tail + self.size)
    }

    pub fn is_empty(&self) -> bool {
        (self.head) == (self.tail)
    }

    pub fn used(&self) -> usize {
        self.head - self.tail
    }

    pub fn unused(&self) -> usize {
        self.size - self.used()
    }

    fn update_head_tail(&mut self) {
        if self.tail >= self.size {
            self.head %= self.size;
            self.tail %= self.size;
        }
    }

    pub fn push(&mut self, value: T) -> Result<()> {
        if self.is_full() {
            return Err(RingBufferError::RingBufferFull);
        }

        self.buf[self.head % self.size].replace(value);
        self.head += 1;

        Ok(())
    }

    pub fn pop(&mut self) -> Option<T> {
        if self.is_empty() {
            return None;
        }

        let ret = self.buf[self.tail % self.size].take();
        self.tail += 1;
        self.update_head_tail();
        ret
    }

    fn push_uncheck(&mut self, value: T) {
        self.buf[self.head % self.size].replace(value);
        self.head += 1;
    }

    pub fn pushv(&mut self, values: Vec<T>) -> Result<()> {
        if self.unused() < values.len() {
            return Err(RingBufferError::RingBufferFull);
        }

        for value in values {
            self.push_uncheck(value)
        }
        Ok(())
    }

    pub fn popv(&mut self, max_num: usize) -> Option<Vec<T>> {
        let mut buffer = Vec::with_capacity(max_num);

        for _ in 0..max_num {
            if let Some(value) = self.pop() {
                buffer.push(value);
            } else {
                break;
            }
        }
        if !buffer.is_empty() {
            Some(buffer)
        } else {
            None
        }
    }
}

impl<T: Debug> Debug for RingBuffer<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RingBuffer")
            .field("head", &self.head)
            .field("tail", &self.tail)
            .field("size", &self.size)
            .field("buf", &self.buf)
            .finish()
    }
}

// fn main() {

// }

#[cfg(test)]
mod tests {
    use crate::RingBufferError;

    use super::{Result, RingBuffer};

    #[test]
    fn test_init() -> Result<()> {
        let size = 5;

        #[cfg(not(feature = "no_std"))]
        println!("using std");

        // #[cfg(feature = "no_std")]
        // println!("using core");

        let mut ring: RingBuffer<i32> = RingBuffer::init(size);
        assert_eq!(ring.unused(), size);
        assert_eq!(ring.used(), 0);
        assert!(ring.is_empty());
        assert!(!ring.is_full());
        assert_eq!(ring.pop(), None);
        assert_eq!(ring.buf, vec![None; size]);

        Ok(())
    }

    #[test]
    fn test_init_with_vec() -> Result<()> {
        let buf = vec![None; 10];
        let mut ring = RingBuffer::init_with_vec(buf);

        ring.push(1)?;
        ring.push(2)?;
        ring.push(3)?;

        assert_eq!(Some(1), ring.pop());
        assert_eq!(Some(2), ring.pop());
        assert_eq!(Some(3), ring.pop());
        assert_eq!(None, ring.pop());

        Ok(())
    }

    #[test]
    fn test_init_with_box() -> Result<()> {
        let buf: Box<[Option<i32>; 5]> = Box::new([None; 5]);
        let mut ring = RingBuffer::init_with_box(buf);

        ring.push(1)?;
        ring.push(2)?;
        ring.push(3)?;
        ring.push(4)?;

        assert_eq!(Some(1), ring.pop());
        assert_eq!(Some(2), ring.pop());
        assert_eq!(Some(3), ring.pop());
        assert_eq!(Some(4), ring.pop());
        assert_eq!(None, ring.pop());

        Ok(())
    }

    #[test]
    fn test_push_full() -> Result<()> {
        let size = 5;
        let mut ring = RingBuffer::init(size);

        ring.push(1)?;
        ring.push(2)?;
        ring.push(3)?;
        ring.push(4)?;
        ring.push(5)?;

        assert!(ring.is_full());
        assert!(!ring.is_empty());

        if let Err(e) = ring.push(6) {
            assert_eq!(RingBufferError::RingBufferFull, e);
        } else {
            panic!("System Error!");
        }

        Ok(())
    }

    #[test]
    fn test_push_pop() -> Result<()> {
        let size = 5;
        let mut ring = RingBuffer::init(size);

        ring.push(1)?;
        ring.push(2)?;
        ring.push(3)?;
        ring.push(4)?;
        ring.push(5)?;

        assert_eq!(Some(1), ring.pop());
        assert_eq!(Some(2), ring.pop());
        assert_eq!(Some(3), ring.pop());
        assert_eq!(Some(4), ring.pop());
        assert_eq!(Some(5), ring.pop());
        assert_eq!(None, ring.pop());

        assert!(!ring.is_full());
        assert!(ring.is_empty());

        Ok(())
    }

    #[test]
    fn test_pushv_full() -> Result<()> {
        let size = 5;
        let data = vec![1, 2, 3, 4, 5];
        let mut ring = RingBuffer::init(size);

        ring.pushv(data)?;
        assert!(ring.is_full());

        if let Err(e) = ring.push(6) {
            assert_eq!(RingBufferError::RingBufferFull, e);
        } else {
            panic!("System Error!");
        }
        if let Err(e) = ring.pushv(vec![6, 7, 8, 9, 10]) {
            assert_eq!(RingBufferError::RingBufferFull, e);
        } else {
            panic!("System Error!");
        }

        Ok(())
    }

    #[test]
    fn test_pushv_popv() -> Result<()> {
        let size = 5;
        let data = vec![1, 2, 3, 4, 5];
        let mut ring = RingBuffer::init(size);

        ring.pushv(data)?;

        assert!(ring.is_full());

        assert_eq!(Some(vec![1, 2, 3]), ring.popv(3));
        assert_eq!(Some(vec![4, 5]), ring.popv(3));
        assert_eq!(None, ring.popv(3));

        Ok(())
    }

    #[test]
    fn test_head_mirror_index() -> Result<()> {
        let size = 5;
        let data = vec![1, 2, 3, 4, 5];
        let mut ring = RingBuffer::init(size);
        ring.pushv(data)?;

        assert_eq!(ring.used(), 5);
        assert_eq!(ring.unused(), 0);

        assert_eq!(Some(1), ring.pop());
        assert_eq!(Some(2), ring.pop());
        assert_eq!(5, ring.head);
        assert_eq!(2, ring.tail);

        ring.push(6)?;
        assert!(!ring.is_empty());
        assert!(!ring.is_full());
        assert_eq!(6, ring.head);

        ring.push(7)?;
        assert!(ring.is_full());
        assert_eq!(7, ring.head);

        assert_eq!(Some(vec![3, 4, 5]), ring.popv(3));
        assert_eq!(2, ring.head);
        assert_eq!(0, ring.tail);

        Ok(())
    }
}
