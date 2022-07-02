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
            matcher text not null,
            ntypes text not null,
            max_len integer not null,
            lambda integer not null,
            cpu double precision not null
        );
        create table means(
            matcher text not null,
            ntypes text not null,
            max_len integer not null,
            lambda integer not null,
            cpu double precision not null,
            cpu_dev double precision not null,
            primary key(matcher, ntypes, max_len, lambda)
        );
    """
    con.executescript(sql)

def insert_raw_data(con, file):
    with open(file, newline='') as csvfile:
        reader = csv.DictReader(csvfile)
        rows = [(
            r['matcher'],r['ntypes'],
            int(r['max_len']),int(r['lambda']),float(r['cpu'])
        ) for r in reader]
    con.executemany("""
        insert into raw_data(matcher,ntypes,max_len,lambda,cpu)
        values(?, ?, ?, ?, ?);
    """, rows)
    con.commit()

def insert_means(con):
    con.create_function('std_dev_', 3, std_dev_)
    sql = """
        insert into means(matcher,ntypes,max_len,lambda,cpu, cpu_dev)
        select matcher,ntypes,max_len,lambda,
               avg(cpu), std_dev_(avg(cpu*cpu), avg(cpu), count(*))
        from raw_data 
        group by matcher,ntypes,max_len,lambda;
    """
    con.execute(sql)
    con.commit()

def get_rows(cur, matcher, ntypes):
    sql = """
        select max_len, lambda, cpu, cpu_dev 
        from means where matcher = ? and ntypes = ?
    """
    cur.execute(sql, (matcher, ntypes))
    return [{
        'max_len':r[0],
        'lambda':r[1],
        'cpu':r[2],
        'cpu_dev':r[3]
    } for r in cur.fetchall()]

def extract_lambda_data(rows0, l):
    rows = [r for r in rows0 if int(r['lambda']) == l]
    return (l, [int(r['max_len']) for r in rows],
        [float(r['cpu']) for r in rows], [float(r['cpu_dev']) for r in rows]
    )

def lam_plot(ax, con, matcher, ntypes, lambdas, title):
    rows = get_rows(con, matcher, ntypes)
    pdata = [extract_lambda_data(rows, l) for l in lambdas]
    for data in pdata:
        l, x, y, e = data
        ax.errorbar(x, y, yerr=e, fmt=".", label=f'λ={l}')
    ax.set_title(title)
    ax.set_xlabel('max length')
    ax.set_ylabel('cpu time [s]')
    ax.legend()
    print(f'Created plot {title}')

con = sqlite3.connect(':memory:')
print('creatint tables')
create_tables(con)
print('reading data')
insert_raw_data(con, 'raw_mesurements.csv')
print('computing averages and standard deviations')
insert_means(con)
cur = con.cursor()

print('Creating plots')

fig, axs = plt.subplots(3,2, figsize=(6, 9), constrained_layout=True)
lam_plot(axs[0,0], cur, 'match_list', 'basic', [1,2,5,10,20,25,30], 'current')
lam_plot(axs[0,1], cur, 'match_list', 'aux', [1,2,5,10, 20,25,30], 'current/ext')
lam_plot(axs[1,0], cur, 'match_list_ns', 'basic', [1,2,3,4,5, 6,7,8], 'abstract')
lam_plot(axs[1,1], cur, 'match_list_ns', 'aux', [1,2,3,4,5, 6,7,8], 'abstract/ext')
lam_plot(axs[2,0], cur, 'match_list_nsc', 'basic', [1,2,3,4], 'concrete')
lam_plot(axs[2,1], cur, 'match_list_nsc', 'aux', [1,2,3], 'concrete/ext')

cur.close()
con.commit()
con.close()

print('Saving')
fig.savefig('fig2.png', dpi=300)

print('Finishing')


