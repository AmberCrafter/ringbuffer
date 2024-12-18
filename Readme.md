# ringbuffer
---
Simple ring buffer.

# Requirements
---
* Support alloc
* Support vec


# Features
---
* default: []
* all: select all features, except: [no_std]
* no_std: support no_std


# Usage
---

```rust
use ringbuffer::RingBuffer;

fn ring_value() {
    let size = 10;
    let mut ring = RingBuffer::init(size);

    ring.push(1);
    assert_eq!(Some(1), ring.pop());
}

fn ring_vector() {
    let size = 10;
    let mut ring = RingBuffer::init(size);

    let data = vec![1,2,3];
    ring.pushv(data);

    assert_eq!(Some(vec![1,2]), ring.popv(2));
}

fn ring_with_vector() {
    let buf = vec![None; 5];
    let mut ring = RingBuffer::init_with_vec(buf);
    ring.push(1);
    assert_eq!(Some(1), ring.pop());
    assert_eq!(None, ring.pop());
}

fn main() {
    ring_value();
    ring_vector();
    ring_with_vector();
}
```

