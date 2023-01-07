import csv 
import matplotlib.pyplot as plt
import sqlite3
import math

def pop_cor(N):
    if N==1:
        return 0
    else:
        return float(N)/(N-1)

def std_dev_(smean, mean, N):
    buf = smean-mean*mean 
    cor = pop_cor(N)
    return math.sqrt(cor * buf)

def create_tables(con):
    sql = """
        create table raw_data (
            id integer primary key,
            opt text not null, 
            success text,
            size integer not null, 
            parameter integer not null, 
            nsols double precision not null, 
            cpu double precision not null
        );
        create table means(
            opt text not null, 
            size integer not null, 
            parameter integer not null, 
            nsols double precision not null, 
            nsols_dev double precision not null,
            cpu_by_nsols double precision not null,
            cpu_by_nsols_dev double precision not null,
            primary key(opt, size, parameter)
        );
    """
    con.executescript(sql)

def insert_raw_data(con, file):
    with open(file, newline='') as csvfile:
        reader = csv.DictReader(csvfile)
        rows = [(
            r['opt'], r['success'], int(r['size']), int(r['parameter']), 
            float(r['nsols']),float(r['cpu'])
        ) for r in reader]
    con.executemany("""
        insert into raw_data(opt, success, size, parameter, nsols, cpu)
        values(?, ?, ?, ?, ?, ?);
    """, rows)
    con.commit()

def insert_means(con):
    con.create_function('std_dev_', 3, std_dev_)
    sql = """
        insert into means(
            opt, size, parameter, nsols, nsols_dev,
            cpu_by_nsols, cpu_by_nsols_dev)
        select opt, size, parameter,
               avg(nsols), std_dev_(avg(nsols*nsols), avg(nsols), count(*)),
               avg(cpu_sols), 
               std_dev_(avg(cpu_sols*cpu_sols), avg(cpu_sols), count(*))
        from (
            select id, opt, size, parameter, nsols, cpu,
                   cpu/(case when nsols=0 then 1 else nsols end) as cpu_sols
            from raw_data
        ) k
        group by opt, size, parameter;
    """
    con.execute(sql)
    con.commit()

def save_fails(con, file):
    sql = """
        select opt, parameter, count(*) as n
        from raw_data 
        where success='timeout'
        group by opt, parameter;
    """
    cur = con.execute(sql)
    with open(file, 'w') as f:
        for r in cur.fetchall():
            f.write(f'{r[0]}, {r[1]}: {r[2]}\n')
    cur.close()

def get_params(con, opt):
    sql = """
        select distinct parameter
        from means where opt = ?;
    """
    cur=con.execute(sql, (opt,))
    res = [r[0] for r in cur.fetchall()]
    cur.close()
    return res

def get_rows(con, opt, param):
    sql = """
        select size, nsols, nsols_dev, cpu_by_nsols, cpu_by_nsols_dev
        from means where opt = ? and parameter = ?
    """
    cur = con.execute(sql, (opt, param))
    res = [{
            'size': int(r[0]),
            'nsols': float(r[1]),
            'nsols_dev': float(r[2]),
            'cpu_by_nsols': float(r[3]),
            'cpu_by_nsols_dev': float(r[4])
    } for r in cur.fetchall()]
    cur.close()
    return res

def reshape(rows, param, attrs):
    return [param] + [[r[x] for r in rows] for x in attrs]

def reshape_nsols(rows, param):
    return reshape(rows, param, ['size', 'nsols', 'nsols_dev'])

def reshape_cpu(rows, param):
    return reshape(rows, param, ['size', 'cpu_by_nsols', 'cpu_by_nsols_dev'])

def get_data(con, opt, reshape_):
    params = get_params(con, opt)
    for p in params:
        rows = get_rows(con, opt, p)
        yield reshape_(rows, p)

def part_plot(ax, con, opt, reshape_, title, y_label):
    for data in get_data(con, opt, reshape_):
        p, x, y, e = data 
        ax.errorbar(x, y, yerr=e, fmt=".", label=f'p={p}')
    ax.set_title(title)
    ax.set_xlabel('Length of stream')
    ax.set_ylabel(y_label)
    ax.legend()
    print(f'Created plot {title}')

def create_plot(con, reshape_, y_label, file):
    fig, axs = plt.subplots(2,2, figsize=(6, 6), constrained_layout=True)
    part_plot(axs[0,0], con, 'd20', reshape_, 'Pattern 1, Δ=20p', y_label)
    part_plot(axs[0,1], con, 'd40', reshape_, 'Pattern 1, Δ=40p', y_label)
    part_plot(axs[1,0], con, 'd20_nm', reshape_, 'Pattern 2, Δ=20p', y_label)
    part_plot(axs[1,1], con, 'd40_nm', reshape_, 'Pattern 2, Δ=40p', y_label)
    fig.savefig(file, dpi=300)
    print(f'Saved file {file}')

with sqlite3.connect(':memory:') as con:
    print('creating tables')
    create_tables(con)
    print('reading data')
    insert_raw_data(con, 'test.csv')
    print('computing averages and standard deviations')
    insert_means(con)
    print('Creating plots')
    create_plot(con, reshape_nsols, '# of matchings', 'nsols.png')
    create_plot(con, reshape_cpu, 'Cpu per matching [s]', 'cpu.png')
    save_fails(con, 'fails.txt')

print('Finishing')


