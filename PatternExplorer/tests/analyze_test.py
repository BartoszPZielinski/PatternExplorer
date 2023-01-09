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

def save_fails(con, file):
    sql = """
        select opt, parameter, count(*) as n
        from raw_data where success='timeout'
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
        from raw_data where opt = ?;
    """
    cur=con.execute(sql, (opt,))
    res = [r[0] for r in cur.fetchall()]
    cur.close()
    return res

def shape_plot_data(con, opt, param, sql):
    cur = con.execute(sql, (opt, param))
    rows = [(int(r[0]), float(r[1]), float(r[2])) for r in cur.fetchall()]
    cur.close()
    return [param] + [[x[i] for x in rows] for i in [0,1,2]]

def get_cpu(con, opt, param):
    return shape_plot_data(con, opt, param, """
        select size, avg(cpu), 
               std_dev_(avg(cpu*cpu), avg(cpu), count(*))
        from raw_data
        where opt = ? and parameter = ?
        group by size
    """)

def get_nsols(con, opt, param):
    return shape_plot_data(con, opt, param, """
        select size, avg(nsols), 
               std_dev_(avg(nsols*nsols), avg(nsols), count(*))
        from raw_data
        where opt = ? and parameter = ? and success='success'
        group by size
    """)

def part_plot(ax, con, opt, get_data_, title, y_label):
    params = get_params(con, opt)
    for p in params:
        p, x, y, e = get_data_(con, opt, p)
        ax.errorbar(x, y, yerr=e, fmt=".", label=f'p={p}')
    ax.set_ylim(bottom=0.0)
    ax.set_xlim(left=0)
    ax.set_title(title)
    ax.set_xlabel('Length of stream')
    ax.set_ylabel(y_label)
    ax.legend()
    print(f'Created plot {title}')

def create_plot(con, get_data_, y_label, file):
    fig, axs = plt.subplots(2,2, figsize=(6, 6), constrained_layout=True)
    part_plot(axs[0,0], con, 'd20', get_data_, 'Pattern 1, Δ=20p', y_label)
    part_plot(axs[0,1], con, 'd40', get_data_, 'Pattern 1, Δ=40p', y_label)
    part_plot(axs[1,0], con, 'd20_nm', get_data_, 'Pattern 2, Δ=20p', y_label)
    part_plot(axs[1,1], con, 'd40_nm', get_data_, 'Pattern 2, Δ=40p', y_label)
    fig.savefig(file, dpi=300)
    print(f'Saved file {file}')

with sqlite3.connect(':memory:') as con:
    create_tables(con)
    con.create_function('std_dev_', 3, std_dev_)
    print('reading data')
    insert_raw_data(con, 'test.csv')
    create_plot(con, get_nsols, '# of matchings', 'nsols.png')
    create_plot(con, get_cpu, 'Cpu [s]', 'cpu.png')
    save_fails(con, 'fails.txt')

print('OK')


