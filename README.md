# state-department

[![crates.io](https://img.shields.io/crates/v/state-department.svg)](https://crates.io/crates/state-department)
[![docs.rs](https://docs.rs/state-department/badge.svg)](https://docs.rs/state-department/)
[![License](https://img.shields.io/crates/l/state-department)](https://github.com/WilliamVenner/state-department)
[![Workflow Status](https://github.com/WilliamVenner/state-department/workflows/ci/badge.svg)](https://github.com/WilliamVenner/state-department/actions?query=workflow%3A%22ci%22)

An implementation of state management and dependency injection for Rust,
designed for use as a gracefully destructible manager of global state.

This library is designed for large, complex applications where you need
to access shared state across many different parts of your program,
perhaps with the additional desire to gracefully shutdown/destruct/drop
said state.

# Features

-   **Thread Safe**: The state manager can be accessed from multiple threads
    simultaneously.
-   **Async Initialization**: The state manager can be initialized
    asynchronously via [`State::init_async`] and [`State::try_init_async`].
-   **Graceful Dropping**: Global state can be gracefully dropped when it is no
    longer needed, returning whether there are still held references to the state.
-   **Lazy Initialization**: Global state can be initialized immediately or lazily
    via [`StateRegistry::insert_lazy`].

# Example Use Case

Imagine your program makes use of an SQLite database stored on disk, and you
need to access this database from many different parts of your program.

Because the database is stored to the disk, you want to ensure that the
database is properly closed and flushed to disk when your program exits.

If you store the database connection in a `static` variable, it can't be
dropped without having to ["shotgun"] a significant amount of boilerplate
code around your codebase, which can be error-prone and tedious to maintain.

`state-department` aims to solve this problem by providing a safe and
ergonomic way to manage global state in your program, with the ability to
gracefully drop the global state when your program exits.

In this example use case, you could use `state-department` to store the
database connection in [`State`], and then gracefully drop the state when
your program exits, thereby closing the database connection and flushing
any changes to disk.

["shotgun"]: https://en.wikipedia.org/wiki/Shotgun_surgery

# Alternative Design Pattern

This design pattern is one of many available patterns for managing state
in Rust. However, some believe that this pattern is inappropriate and
recommend simply initializing all of your program's state in your
`main` function as `let` variables and passing them down as function
arguments to the parts of your program that need them.

This guarantees that all of your program's state is properly initialized and
dropped in the correct order.

Therefore, **I recommend this approach for smaller applications**.

However, because this can lead to a lot of boilerplate and can grow to
be difficult and tedious to refactor and build upon, `state-department`
may be more appropriate for larger, more complex applications.

# Example

```rust
use state_department::State;

/// Your program's global state.
pub static STATE: State = State::new();

struct Foo {
    bar: i32
}
impl Drop for Foo {
    fn drop(&mut self) {
        println!("Dropping Foo!");
    }
}

// Initialize the global state.
let lifetime = STATE.init(|state| {
    // Insert an entry for `Foo` into the global state.
    state.insert(Foo { bar: 42 });
});

// Retrieve the `Foo` entry from the global state.
let foo = STATE.get::<Foo>();

assert_eq!(foo.bar, 42);

// Make sure we're not holding a reference to the state (via `foo`).
drop(foo);

// Gracefully drop the global state.
if lifetime.try_drop().is_err() {
    if cfg!(debug_assertions) {
        panic!("BUG: Global state still has held references")
    } else {
        eprintln!("BUG: Global state still has held references");
    }
}

// > Dropping Foo!
```

# Drop Behavior

After initializing the state with [`State::init`] or [`State::try_init`],
you will receive a [`StateLifetime`]. This acts as the "lifetime" of your
state; if this value is dropped, your state will be dropped with it,
**provided that there are no currently held references to the state.**

If there are still held references to the state, nothing will happen. The
values held within the state will not be dropped until the corresponding
[`State`] is also dropped. Note that if your [`State`] is stored
in a `static` variable, **it will never be dropped** and your [`Drop`]
implementations and destructors will therefore never be called.

Because in most cases this is considered a bug in the program,
`state-department` provides a fallible way to gracefully drop the state
yourself at the end of your program via [`StateLifetime::try_drop`].
This gives you an opportunity to raise an error, log a message, or otherwise
handle the situation where there are still held references to your state.
