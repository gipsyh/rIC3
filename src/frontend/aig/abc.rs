use abc_rs::Abc;
use aig::Aig;
use std::{env, mem::take, time::Duration};

fn preprocess(f: String) {
    let mut aig = Aig::from_file(&f);
    let num_input = aig.inputs.len();
    let num_latchs = aig.latchs.len();
    let num_constraints = aig.constraints.len();
    aig.outputs.push(aig.bads[0]);
    aig.bads.clear();
    let latchs = take(&mut aig.latchs);
    for l in latchs.iter() {
        aig.inputs.push(l.input);
        aig.outputs.push(l.next);
    }
    for c in take(&mut aig.constraints) {
        aig.outputs.push(c);
    }
    assert!(aig.inputs.len() == num_input + num_latchs);
    assert!(aig.outputs.len() == 1 + num_latchs + num_constraints);
    let mut abc = Abc::new();
    abc.read_aig(&aig);
    drop(aig);
    abc.execute_command("&get; &fraig -y; &put; orchestrate;");
    let mut abc_aig = abc.write_aig();
    for (i, li) in latchs.iter().enumerate() {
        let mut l = *li;
        l.input = abc_aig.inputs[num_input + i];
        l.next = abc_aig.outputs[1 + i];
        abc_aig.latchs.push(l);
    }
    abc_aig.inputs.truncate(num_input);
    for i in 0..num_constraints {
        abc_aig
            .constraints
            .push(abc_aig.outputs[1 + num_latchs + i]);
    }
    abc_aig.bads.push(abc_aig.outputs[0]);
    abc_aig.outputs.clear();
    assert!(abc_aig.inputs.len() == num_input);
    assert!(abc_aig.latchs.len() == num_latchs);
    assert!(abc_aig.constraints.len() == num_constraints);

    abc_aig.to_file(&f, false);
}

#[allow(unused)]
pub fn abc_preprocess(mut aig: Aig) -> Aig {
    let dir = match env::var("RIC3_TMP_DIR") {
        Ok(d) => d,
        Err(_) => "/tmp/rIC3".to_string(),
    };
    let tmpfile = tempfile::NamedTempFile::new_in(dir).unwrap();
    aig.to_file(tmpfile.path(), false);
    let mut join = procspawn::spawn(
        tmpfile.path().as_os_str().to_str().unwrap().to_string(),
        preprocess,
    );
    if join.join_timeout(Duration::from_secs(5)).is_ok() {
        aig = Aig::from_file(tmpfile.path());
    } else {
        println!("abc preprocess timeout");
        let _ = join.kill();
    }
    drop(tmpfile);
    aig
}
