use criterion::{criterion_group, criterion_main, Criterion};
use std::hint::black_box;

#[derive(Default)]
pub struct Foo {
    pub a: String,
    pub b: String,
    pub c: String,
    pub d: String,
    pub e: String,
    pub f: String,
}

#[derive(Default)]
pub struct Bar {
    pub a: String,
    pub b: String,
    pub c: String,
    pub d: String,
    pub e: String,
    pub f: String,
}

#[derive(Default)]
pub struct Baz {
    pub a: String,
    pub b: String,
    pub c: String,
    pub d: String,
    pub e: String,
    pub f: String,
}

fn synchronous(c: &mut Criterion) {
    c.bench_function("synchronous", |b| {
        let state = state_department::State::new();

        let _state = state.init(|state| {
            state.insert::<Foo>(black_box(Foo::default()));
            state.insert_lazy::<Bar, _>(|| black_box(Bar::default()));
        });

        let _ = state.get::<Foo>();
        let _ = state.get::<Bar>();

        b.iter(|| black_box(state.get::<Foo>()));
        b.iter(|| black_box(state.get::<Bar>()));
    });
}

fn asynchronous(c: &mut Criterion) {
    c.bench_function("asynchronous", |b| {
        let rt = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();

        let state = state_department::AsyncState::new();

        let _state = rt.block_on(async {
            let _state = state
                .init_async(async |state| {
                    state.insert::<Foo>(black_box(Foo::default()));
                    state.insert_lazy::<Bar, _>(|| black_box(Bar::default()));
                    state.insert_async_lazy::<Baz, _>(async { black_box(Baz::default()) });
                })
                .await;

            let _ = state.get::<Foo>().await;
            let _ = state.get::<Bar>().await;
            let _ = state.get::<Baz>().await;

            _state
        });

        let mut b = b.to_async(rt);

        b.iter(|| black_box(state.get::<Foo>()));
        b.iter(|| black_box(state.get::<Bar>()));
        b.iter(|| black_box(state.get::<Baz>()));
    });
}

criterion_group!(benches, synchronous, asynchronous);
criterion_main!(benches);
