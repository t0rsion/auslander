use std::hint::black_box;

use auslander::algebra::{commutative_square, linear_an};
use auslander::family::{CompiledModuleFamily, FamilyFixedEntry, FamilyParameter};
use auslander::field::{Fp, PrimeField};
use auslander::hom::{hom, hom_dim};
use auslander::interface::{InterfaceFamilyHomPlan, InterfacePartition};
use auslander::linalg::DenseMat;
use auslander::module::{Module, direct_sum};
use auslander::quiver::ArrowId;
use auslander::radical::{radical, socle, top};

use super::perf_support::{Runner, core_fixtures, f5, regular};

pub(crate) fn module_layer(r: &mut Runner) {
    for (name, algebra) in core_fixtures() {
        let a = regular(&algebra);
        let dims = a.dim_vector().to_vec();
        let maps: Vec<DenseMat> = (0..algebra.quiver().num_arrows())
            .map(|i| a.map(ArrowId(i as u32)).clone())
            .collect();
        r.case("module", &format!("Module::new A {name}"), 1, || {
            black_box(
                Module::new(algebra.clone(), dims.clone(), maps.clone()).expect("A is a module"),
            );
        });
        r.case("module", &format!("hom(A, A) {name}"), 1, || {
            black_box(hom(&a, &a).expect("one algebra"));
        });
        r.case("module", &format!("hom_dim(A, A) {name}"), 1, || {
            black_box(hom_dim(&a, &a).expect("one algebra"));
        });
        r.case("module", &format!("radical(A) {name}"), 1, || {
            black_box(radical(&a));
        });
        r.case("module", &format!("socle(A) {name}"), 1, || {
            black_box(socle(&a));
        });
        r.case("module", &format!("top(A) {name}"), 1, || {
            black_box(top(&a));
        });

        let longest = algebra
            .basis()
            .iter()
            .max_by_key(|w| w.len())
            .expect("a basis is nonempty")
            .clone();
        r.case(
            "module",
            &format!("word_action len={} {name}", longest.len()),
            1,
            || {
                black_box(a.word_action(&longest).expect("a basis word is a path"));
            },
        );

        let p0 = Module::projective(&algebra, 0);
        for k in [2usize, 4, 8, 16] {
            let parts: Vec<&Module> = (0..k).map(|_| &p0).collect();
            r.case("module", &format!("direct_sum k={k} {name}"), 1, || {
                black_box(direct_sum(&parts));
            });
        }
    }
}

pub(crate) fn compiled_families(r: &mut Runner) {
    for dimension in [2, 4, 8] {
        let fixture = square_family(dimension, f5());
        let name = fixture.name.as_str();
        r.case("family", &format!("compile family {name}"), 1, || {
            black_box(fixture.spec.compile());
        });
        benchmark_family(r, &fixture);
    }

    for interface_width in [2, 4, 8] {
        let fixture = interface_family(4, interface_width, f5());
        let name = fixture.family.name.as_str();
        r.case("family", &format!("compile family {name}"), 1, || {
            black_box(fixture.family.spec.compile());
        });
        r.case(
            "family",
            &format!("compile interface plan {name}"),
            1,
            || {
                black_box(
                    InterfaceFamilyHomPlan::compile(
                        &fixture.family.family,
                        &fixture.partition,
                        &fixture.family.source,
                    )
                    .expect("the source is a valid anchor"),
                );
            },
        );
        r.case("family", &format!("Hom fixed-interface {name}"), 1, || {
            black_box(
                fixture
                    .plan
                    .compute(&fixture.family.source, &fixture.family.target)
                    .expect("the interface plan accepts both fibers"),
            );
        });
        r.case(
            "family",
            &format!("Hom fixed-interface modules {name}"),
            1,
            || {
                black_box(
                    fixture
                        .plan
                        .compute_modules(&fixture.source_module, &fixture.target_module)
                        .expect("the interface plan accepts both modules"),
                );
            },
        );
        r.case("family", &format!("Hom generic {name}"), 1, || {
            black_box(
                fixture
                    .family
                    .family
                    .hom_space_generic(&fixture.family.source, &fixture.family.target)
                    .expect("two fibers share their algebra"),
            );
        });
    }
}

struct FamilyFixture {
    name: String,
    spec: FamilySpec,
    family: CompiledModuleFamily,
    source: Vec<Fp>,
    target: Vec<Fp>,
}

struct FamilySpec {
    algebra: std::sync::Arc<auslander::algebra::Algebra>,
    dimensions: Vec<usize>,
    fixed: Vec<FamilyFixedEntry>,
    parameters: Vec<FamilyParameter>,
}

impl FamilySpec {
    fn compile(&self) -> CompiledModuleFamily {
        CompiledModuleFamily::new(
            &self.algebra,
            self.dimensions.clone(),
            self.fixed.clone(),
            self.parameters.clone(),
        )
        .expect("the family specification has a valid layout")
    }
}

struct InterfaceFixture {
    family: FamilyFixture,
    partition: InterfacePartition,
    plan: InterfaceFamilyHomPlan,
    source_module: Module,
    target_module: Module,
}

fn benchmark_family(r: &mut Runner, fixture: &FamilyFixture) {
    let name = fixture.name.as_str();
    r.case("family", &format!("specialize compiled {name}"), 1, || {
        black_box(
            fixture
                .family
                .specialize(&fixture.source)
                .expect("the source fiber satisfies the relation"),
        );
    });
    r.case("family", &format!("specialize generic {name}"), 1, || {
        black_box(
            fixture
                .family
                .specialize_generic(&fixture.source)
                .expect("the source fiber satisfies the relation"),
        );
    });
    r.case("family", &format!("Hom compiled {name}"), 1, || {
        black_box(
            fixture
                .family
                .hom_space(&fixture.source, &fixture.target)
                .expect("two fibers share their algebra"),
        );
    });
    r.case("family", &format!("Hom generic {name}"), 1, || {
        black_box(
            fixture
                .family
                .hom_space_generic(&fixture.source, &fixture.target)
                .expect("two fibers share their algebra"),
        );
    });
}

fn square_family(dimension: usize, field: PrimeField) -> FamilyFixture {
    let algebra = commutative_square(field);
    let parameters = (0..algebra.quiver().num_arrows())
        .flat_map(|arrow| {
            (0..dimension).map(move |diagonal| {
                FamilyParameter::new(
                    format!("x{arrow}_{diagonal}"),
                    ArrowId(arrow as u32),
                    diagonal,
                    diagonal,
                )
            })
        })
        .collect();
    let spec = FamilySpec {
        algebra,
        dimensions: vec![dimension; 4],
        fixed: Vec::new(),
        parameters,
    };
    let family = spec.compile();
    let source = vec![field.one(); family.parameters().len()];
    FamilyFixture {
        name: format!("square-diagonal-dimension-{dimension}-f5"),
        spec,
        target: source.clone(),
        source,
        family,
    }
}

fn interface_family(
    dimension: usize,
    interface_width: usize,
    field: PrimeField,
) -> InterfaceFixture {
    let algebra = linear_an(16, field);
    let parameter_arrow = ArrowId(7);
    let fixed = (0..algebra.quiver().num_arrows())
        .filter(|&arrow| arrow as u32 != parameter_arrow.0)
        .flat_map(|arrow| {
            (0..dimension).map(move |diagonal| {
                FamilyFixedEntry::new(ArrowId(arrow as u32), diagonal, diagonal, field.one())
            })
        })
        .collect();
    let parameters = (0..dimension)
        .flat_map(|row| {
            (0..dimension).map(move |column| {
                FamilyParameter::new(format!("x{row}_{column}"), parameter_arrow, row, column)
            })
        })
        .collect();
    let spec = FamilySpec {
        algebra: algebra.clone(),
        dimensions: vec![dimension; 16],
        fixed,
        parameters,
    };
    let family = spec.compile();
    let start = (16 - interface_width) / 2;
    let end = start + interface_width;
    let left: Vec<u32> = (0..start as u32).collect();
    let interface: Vec<u32> = (start as u32..end as u32).collect();
    let right: Vec<u32> = (end as u32..16).collect();
    let partition = InterfacePartition::new(&algebra, &left, &interface, &right)
        .expect("the interface separates the two interiors");
    let source = parameter_values(dimension, field, 1, 0);
    let target = parameter_values(dimension, field, 2, 1);
    let plan = InterfaceFamilyHomPlan::compile(&family, &partition, &source)
        .expect("the source is a valid anchor");
    let source_module = family
        .specialize(&source)
        .expect("the source fiber satisfies the relation");
    let target_module = family
        .specialize(&target)
        .expect("the target fiber satisfies the relation");
    InterfaceFixture {
        family: FamilyFixture {
            name: format!("a16-dimension-{dimension}-interface-{interface_width}-f5"),
            spec,
            family,
            source,
            target,
        },
        partition,
        plan,
        source_module,
        target_module,
    }
}

fn parameter_values(
    dimension: usize,
    field: PrimeField,
    multiplier: usize,
    offset: usize,
) -> Vec<Fp> {
    let modulus = field.modulus() as usize;
    (0..dimension * dimension)
        .map(|index| field.elem(((multiplier * index + offset) % modulus) as i64))
        .collect()
}
