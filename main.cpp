//#include <graphics.h>
#include <stdio.h>
#include <iostream>
#include <vector>
#include <cstring>
#include <fstream>
#include<Windows.h>
#include <algorithm>
#include <fstream>
#include <string>
#include <stack>
#include <cstdio>
#include <vector>
#include <sstream>

using namespace std;
namespace sta{
//��ջ
stack<int> state_stack;
stack<int> true_stack;
stack<int> false_stack;
stack<char> sign_stack;
stack<string> op_stack;
stack<string> con_stack;
stack<string> tempvar;
int flag_false=0;
vector<vector<string> > quaternary_list;//������¼�������ɵ���Ԫʽ
int var=0;
struct var_and_type
{
	string name;
	string data;//
	char type;//1Ϊbool��2Ϊchar��3Ϊint,4 float 5 double 6 string
    int priority;
	//֮����Ҫ��Ĭ��������Ϊ-1������Ϊ�����������ͻ����ʱ��Ҫ����-1��Ԫ�ؿ�ʼ���л���
	var_and_type()
	{
		type = '-1';//Ĭ������Ϊ-1
	}

	var_and_type(string s,string d, char t,int p)
	{
		name=s;
		data = d;
		type = t;
		priority=p;
	}

};

vector<var_and_type> var_list;
char G[1000][1000];     //���ķ�
int length[1000];    //�ķ��ĳ���
int number=0;    //�ķ��ĸ���
bool isV[1000];      //buffer of input
char Vn[1000];        //���ս��
int size_vn=0;
char Vt[300];       //�ս��
int size_vt=0;
bool first[600][300];    //first��
char buffer[1500];
int size=0;
struct T        //ת����  ��Ŀ��ת��
{
		int begin;
		int next;
		char ch;
};
struct project      //��Ŀ��
{
		int num;
		int now;
		char search;
};
struct action
{
		char ch;
		int next_state;
};


T trans[1000];
int size_trans=0;
project items[1000][300];
int countw=0;
int size_item[1000];

action action_table[1000][1000];
int size_act_table[1000];

//�ļ�����
ifstream grammar_file;
ifstream input_file;
ofstream items_file;
ofstream out;
ofstream action_file;
ofstream firstset_file;
ofstream procedure_file;
fstream constant;
fstream variation;
ofstream explain;




void get_grammar()     //���ķ�
{
		char nouse,temp;
		int i,j=0;
		G[0][0]='S';    //S��->`S
		length[0]=2;
		for(i=1;grammar_file.peek()!=EOF;++i)
		{
				j=0;
				grammar_file>>temp;
				grammar_file>>nouse>>nouse;
				while(temp!='$')
				{
						G[i][j++]=temp;
						isV[temp]=true;
						grammar_file>>temp;
				}
				length[i]=j;
		}
		number=i;
		G[0][1]=G[1][0];
	 //ASCII���
		for(i=0;i<64;++i)
		{
				if(isV[i])
				{
					 	Vt[size_vt++]=i;
				}
		}
		for(i=65;i<91;++i)
		{
				if(isV[i])
				{
					 	Vn[size_vn++]=i;
				}
		}
		for(i=91;i<128;++i)
		{
				if(isV[i])
				{
					 	Vt[size_vt++]=i;
				}
		}
}
bool Is_in_vn(char a)
{
		for(int i=0;i<size_vn;++i)
		{
				if(Vn[i]==a)
				{
						return true;
				}
		}
		return false;
}
void get_first()
{
		bool done=true;    //�����ܸĵĵط� �Ͳ�ͣ����
		int t,k;
		bool isempty;
		while(done)
		{
				done=false;
				for(int i=1;i<=number;i++)
				{
					 	t=1;
					 	isempty=true;
					 	while(isempty && t<length[i])
					 	{
							 	isempty=false;
							 	if(G[i][t]>='A' && G[i][t]<='Z')
							 	{
										for(k=0;k<=63;++k)
										{
											if(first[G[i][t]-'A'][k]==true && !first[G[i][0]-'A'][k])
											{
													first[G[i][0]-'A'][k]=true;
													done=true;
											}
										}
										if(first[G[i][t]-'A'][64]==true)    //��@��ʾ ��
										{
												isempty=true;
												++t;
										}
										for(k=91;k<128;++k)
										{
											if(first[G[i][t]-'A'][k]==true && first[G[i][0]-'A'][k]==false)
											{
													done=true;
													first[G[i][0]-'A'][k]=true;
											}
										}
								}
								else if(first[G[i][0]-'A'][G[i][t]]==false)
								{
									done=true;
									first[G[i][0]-'A'][G[i][t] ]=true;
								}
					 	}
					 	if(length[i]==t)
					 	{
								first[G[i][0]-'A'][26]=true;
					 	}
				}
		}
}
void write_first_set()
{
		for(int i=0;i<26;++i)
		{
				char ch=char(i+'A');
				if(Is_in_vn(ch))
				{
						/*printf("first(%c)=",ch);
						for(int j=0;j<128;++j)
						{
								if(first[i][j]==true)
								{
										cout<<char(j)<<",";
								}
						}
						cout<<endl;*/
						firstset_file<<"first("<<ch<<")={";
						for(int j=0;j<128;++j)
						{
								if(first[i][j]==true)
								{
										firstset_file<<char(j)<<",";
								}
						}
						firstset_file<<"}"<<endl;
				}
		}
}


void gete_search(project temp)    //�õ���ǰ������
{
		size=0;
		bool flag=true;
		int nownow=temp.now;
		int i;
		while(flag==true)
		{
				flag=false;
				if(nownow+1>=length[temp.num])
				{
						buffer[size++]=temp.search;
						return;
				}
				else if(G[temp.num][nownow+1]<'A' || G[temp.num][nownow+1]>'Z')
				{
								buffer[size++]=G[temp.num][nownow+1];
								return;
				}
				else if(G[temp.num][nownow+1]>='A' && G[temp.num][nownow+1]<='Z')
				{
						for(i=0;i<64;++i)
						{
								if(first[G[temp.num][nownow+1]-'A'][i]==true)
										buffer[size++]=i;
						}
						for(i=91;i<128;++i)
						{
								if(first[G[temp.num][nownow+1]-'A'][i]==true)
								{
										buffer[size++] = i;
								}
						}
						if(first[G[temp.num][nownow+1]-'A'][64]==true)
						{
								++nownow;
								flag=true;
						}
				}
		}
}

bool is_in(project temp,int T)   //��ǰ��Ŀ��Ԫ���Ƿ��ظ�
{
		int i;
		for(i=0;i<size_item[T];++i)
		{
				if(items[T][i].num==temp.num && items[T][i].now==temp.now && items[T][i].search==temp.search)
				{
						return true;
				}
		}
		return false;
}

void e_closure(int T)   //����Ŀ����
{
		project temp;
		int i,j,k;
		for(i=0;i<size_item[T];++i)
		{
			 	if(G[items[T][i].num][items[T][i].now]>='A' && G[items[T][i].num][items[T][i].now]<='Z')
			 	{
					 	for(j=0;j<300;++j)
					 	{
					 		size=0;
					 		if(G[j][0]==G[items[T][i].num][items[T][i].now])
							{
								 		gete_search(items[T][i]);
								 		for(k=0;k<size;++k)
								 		{
												temp.num=j;
												temp.now=1;
												temp.search=buffer[k];
												if(is_in(temp,T)==false)
												{
													 	items[T][size_item[T]++]=temp;
												}
								 		}
							}
					 	}
				}
		}
		return;
}

int is_contained()   //��ǰ��Ŀ�� ����ǰ�Ƚ�
{
		int i;
		int sum=0;
		int j;
		int k;
		for(i=0;i<countw;++i)
		{
			 	sum=0;        //��¼�ж�����ƥ���
			 	if(size_item[countw]==size_item[i])
			 	{
			 		for(j=0;j<size_item[countw];++j)
					{
							for(k=0;k<size_item[i];++k)
							{
								if(items[i][k].num==items[countw][j].num && items[i][k].now==items[countw][j].now && items[i][k].search==items[countw][j].search)
								{
										++sum;
										break;
								}
							}
					}
			 	}
			 	if(sum==size_item[countw])
			 	{
						return i;
			 	}
		}
		return 0;
}
void make_set()
{
		items[0][0].num=0;
		items[0][0].now=1;
		items[0][0].search='#';
		size_item[0]=1;
		e_closure(0);
		project buf[50];
		int buf_size=0;
		project tp;
		int i,j,k;
		int nextt_state;
		items_file<<"I0:"<<endl;
		for(i=0;i<size_item[0];++i)
		{
				items_file<<G[items[0][i].num][0]<<"->"<<G[items[0][i].num]+1<<" , "<<items[0][i].now<<" , "<<items[0][i].search<<endl;
		}
		items_file<<"--------------------------------------------------"<<endl;
	 	int index;
	 	int p;
	 	int t;
		for(index=0;index<countw+1;++index)
		{
				for(j=0;j<size_vt;++j)
				{
						buf_size=0;
						for(p=0;p<size_item[index];++p)
						{
								if(items[index][p].now<length[items[index][p].num] && G[items[index][p].num][items[index][p].now]==Vt[j])
								{
										tp.num=items[index][p].num;
										tp.search=items[index][p].search;
										tp.now=items[index][p].now+1;
										buf[buf_size++]=tp;
								}
						}
						if(buf_size!= 0)    //����һ���µ���Ŀ��
						{
								countw++;
								for(t=0;t<buf_size;++t)
								{
										items[countw][size_item[countw]++]=buf[t];
								}
								e_closure(countw);
								nextt_state=is_contained();        //����count����Ŀ���Ƿ��ظ�
								if(nextt_state!=0)           //�ظ�����ת�������е��Ǹ���Ŀ����ȥ
								{
										size_item[countw--]=0;
										trans[size_trans].begin=index;
										trans[size_trans].next=nextt_state;
										trans[size_trans++].ch=Vt[j];
										//cout<<size_trans<<index<<nextt_state<<Vt[j]<<endl;
								}
								else
								{
										items_file<<"I"<<countw<<":"<<endl;
										for(i=0;i<size_item[countw];++i)
										{
												items_file<<G[items[countw][i].num][0]<<"->"<<G[items[countw][i].num]+1<<" , "<<items[countw][i].now<<" , "<<items[countw][i].search<<endl;
										}
										items_file<<"--------------------------------------------------"<<endl;
										trans[size_trans].begin=index;
										trans[size_trans].next=countw;
										trans[size_trans++].ch=Vt[j];
										//cout<<size_trans<<index<<count<<Vt[j]<<endl;
								}
						}
				}

				for(j=0;j<size_vn;++j)
				{
						buf_size = 0;
						for(p=0;p<size_item[index];++p)
						{
								if(items[index][p].now<length[items[index][p].num] && G[items[index][p].num][items[index][p].now]==Vn[j])
								{
										tp.num=items[index][p].num;
										tp.search=items[index][p].search;
										tp.now=items[index][p].now+1;
										buf[buf_size++]=tp;
								}
						}
						if(buf_size!=0)
						{
								++countw;
								for(t=0;t<buf_size;++t)
								{
										items[countw][size_item[countw]++]=buf[t];
								}
								e_closure(countw);
								nextt_state=is_contained();

								if(nextt_state!=0)
								{
										size_item[countw--]=0;
										trans[size_trans].begin=index;
										trans[size_trans].next=nextt_state;
										trans[size_trans++].ch=Vn[j];
										//cout<<size_trans<<index<<nextt_state<<Vn[j]<<endl;
								}
								else
								{
										items_file<<"I"<<countw<<":"<<endl;
										for(i=0;i<size_item[countw];++i)
										{
												items_file<<G[items[countw][i].num][0]<<"->"<<G[items[countw][i].num]+1<<" , "<<items[countw][i].now<<" , "<<items[countw][i].search<<endl;
										}
										items_file<<"--------------------------------------------------"<<endl;
										trans[size_trans].begin=index;
										trans[size_trans].next=countw;
										trans[size_trans++].ch=Vn[j];
										//cout<<size_trans<<index<<count<<Vn[j]<<endl;
								}
						}
				}
		}
}

void get_action()
{
		int i,j;
		int t1,t2,t;
		char tp;
		for(i=0;i<300;++i)
		{
				size_act_table[i]=0;
		}
		for(i=0;i<=countw;++i)
		{
				for(j=0;j<size_item[i];++j)
				{
					if(items[i][j].now==length[items[i][j].num] || (items[i][j].now==1 && length[items[i][j].num]==2 && G[items[i][j].num][1]=='@'))//��Լ
						{
								action_table[i][size_act_table[i]].ch=items[i][j].search;
								action_table[i][size_act_table[i]++].next_state=items[i][j].num*(-1);
						}
				}
		}
		for(i=0;i<size_trans;++i)
		{
				t1=trans[i].begin;
				t2=trans[i].next;
				tp=trans[i].ch;
				action_table[t1][size_act_table[t1]].ch=tp;
				action_table[t1][size_act_table[t1]++].next_state=t2;
				//cout<<i<<action_table[t1][size_act_table[t1]-1].ch<<action_table[t1][size_act_table[t1]-1].next_state<<endl;
		}
		for(i = 0; i <= countw; ++i)
    	{
	      for(j = 0; j < size_act_table[i]; ++j)
	      {
	            tp=action_table[i][j].ch;
	            t=action_table[i][j].next_state;
	            action_file << "(" << i << "," << tp << "," << t << ")" << endl;
	      }
    }
}
int prio=0;
void write_stack(int x)
{
	stack<int> a;
	prio=0;
	stack<char> c;
	if(x==1)    //״̬
	{
		while(state_stack.empty()==false)
		{
			a.push(state_stack.top());
			state_stack.pop();
		}
		while(a.empty()==false)
		{
			procedure_file<<a.top()<<',';
			state_stack.push(a.top());
			a.pop();
		}
	}
	if(x==2)   //����
	{
		while(sign_stack.empty()==false)
		{
			c.push(sign_stack.top());
			sign_stack.pop();
		}
		while(c.empty()==false)
		{
		    if(c.top()=='{')prio++;
		    if(c.top()=='}')prio--;
			procedure_file<<c.top()<<',';
			sign_stack.push(c.top());
			c.pop();
		}
	}
}
void judge()
{
	char p[] = "�����ɹ���";
	size = 0;
	stack<char> temptype;
	while(input_file>>buffer[size] && buffer[size++] != '#');
    int    work_sta = 0;
    int    index_buf = 0;
    bool   error=false;
    bool   done = false;
    char now_in;
    now_in=buffer[0];
    state_stack.push(0);
    sign_stack.push('#');
    procedure_file<<"״̬ջ                 ����ջ                  ���봮               ACTION                  GOTO"<<endl;
    int i,j,k,m;
    int tp,len;
    int aa;
    while(done == false && error == false)
    {
        work_sta = state_stack.top();
        write_stack(1);
        procedure_file<<"               ";
        write_stack(2);
        procedure_file<<"               ";
        for(i=index_buf;i<size;++i)
        {
        		procedure_file<<buffer[i];
        }
        procedure_file<<"              ";
        char tempe=buffer[index_buf];
		char tempc=buffer[index_buf+1];
        error =  true;
        for(i= 0; i < size_act_table[work_sta];++i)
        {
            if(action_table[work_sta][i].ch ==now_in)
            {
                    error = false;
                    if(action_table[work_sta][i].next_state == 0)
                    {
                                    procedure_file << "YES" << endl;
                                    //printf("YES\n");
                                   // outtextxy(600, 260, p);
                                    done = true;
                                    break;
                    }
                    else if(action_table[work_sta][i].next_state > 0)   //�ƽ�
                    {
                    		procedure_file<<'S'<<action_table[work_sta][i].next_state<<endl;
                    		cout<<'S'<<action_table[work_sta][i].next_state<<endl;

                       	state_stack.push(action_table[work_sta][i].next_state);
                       	sign_stack.push(action_table[work_sta][i].ch);
                        ++index_buf;
                        now_in=buffer[index_buf];
                        break;
                    }
                    else if(action_table[work_sta][i].next_state < 0)
                    {
                       	tp = action_table[work_sta][i].next_state*(-1);
                       	procedure_file<<'r'<<tp<<"              ";
                       	cout<<'r'<<tp<<endl;
                       	len=length[tp]-1;
                       	if(G[tp][1]=='@')
                       	{
                       			--len;
                       	}
                       	stack<int> too;

						vector<string> temp;
						string an;
						//���X�������ɸ�ֵ���
//Q���мӼ��˳�����
//J �߼��������
//T �������
						switch(G[tp][0])
                        {
                        case 'I':
                        	{
							string s;
							s.push_back(sign_stack.top());
                            temp.push_back("header"); temp.push_back("-"); temp.push_back("-"); temp.push_back(s);
                            quaternary_list.push_back(temp);
                            break;}
                        case 'B':
                            temptype.push(sign_stack.top());
                            break;
                        case 'C':
                            {
                            string s;
							s.push_back(sign_stack.top());
							string a;
							a.push_back(temptype.top());
							temp.push_back(s); temp.push_back("-"); temp.push_back("-"); temp.push_back(a);
                            quaternary_list.push_back(temp);
                            break;}
                        case 'D':
                            temptype.push(sign_stack.top());
                            break;
                        case 'N':
							getline(variation,an);
							tempvar.push(an);
							cout<<an;
                            break;
                        case 'T':
                            while(!tempvar.empty()){
                                int i,j;
                                var_and_type a;
                                if(len>3){
                                   temp.push_back(":=");
                                     string value;
                                    string bb=tempvar.top();
                                    if(bb=="int"){
                                   i=temptype.top();
                                   temp.push_back(con_stack.top());
                                   cout<<con_stack.top();
                                    cout<<i;
                                    value=con_stack.top();
                                   temptype.pop();
                                   tempvar.pop();
                                   con_stack.top();
                                }else{temp.push_back(tempvar.top());
                                    cout<<tempvar.top();
                                    i=temptype.top();
                                    value=tempvar.top();
                                   temptype.pop();
                                   tempvar.pop();
                                   }

                                string ba=tempvar.top();
                                temp.push_back("-");
                                if(ba=="int"){
                                   cout<<"�޷���ֵ������";
                                   return;
                                }else{temp.push_back(tempvar.top());
                                    cout<<tempvar.top();
                                    j=temptype.top();
                                 }
                                 quaternary_list.push_back(temp);
                                if(temptype.top()=='z'){
                                    if(i==53||i==51){
                                    a=var_and_type(ba,value,'5',prio);}
                                    else {cout<<"���Ͳ�ƥ�䣬�޷���ֵ"<<endl;return;}
                                }
                                if(temptype.top()=='y'){
                                    if(i==52){
                                    a=var_and_type(ba,value,'4',prio);
                                    }
                                    else {cout<<"���Ͳ�ƥ�䣬�޷���ֵ"<<endl;return;}
                                }
                                if(temptype.top()=='h'){
                                    if(i==51||i==53||i==50){
                                    a=var_and_type(ba,"",'3',prio);
                                    cout<<"dhdhdhdh";
                                    }
                                    else {cout<<"���Ͳ�ƥ�䣬�޷���ֵ"<<endl;return;}
                                }
                                if(temptype.top()=='a'){
                                    if(i==51||i==50){
                                    a=var_and_type(ba,value,'2',prio);}
                                    else {cout<<"���Ͳ�ƥ�䣬�޷���ֵ"<<endl;return;}

                                }
                                if(temptype.top()=='g'){
                                    if(i==51||i==49){
                                    a=var_and_type(ba,value,'1',prio);}
                                    else {cout<<"���Ͳ�ƥ�䣬�޷���ֵ"<<endl;return;}
                                }
                                if(temptype.top()=='s'){
                                    if(i==54){
                                    a=var_and_type(ba,value,'6',prio);}
                                    else {cout<<"���Ͳ�ƥ�䣬�޷���ֵ"<<endl;return;}
                                }
                                vector<var_and_type>::iterator it;
                                if(var_list.size()==0){
                                    cout<<a.name<<"����\n";
                                    var_list.push_back(a);
                                }else{
                                   for(it=var_list.begin();it!=var_list.end();it++){
                                        if(it->name==bb&&it->priority==prio)
                                        {
                                            cout<<it->name<<endl;
                                            printf("�ظ�����\n");
                                            return;
                                        }
                                        if(it->name==bb&&it->priority>prio)
                                        {
                                            cout<<it->name<<endl;
                                            printf("�ñ�ʶ��δ����\n");
                                            return;
                                        }
                                    }
                                    cout<<a.name<<"����\n";
                                    var_list.push_back(a);

                                }
                                tempvar.pop();
                                }else{
                                    var_and_type a;
                                string bb=tempvar.top();
                                cout<<bb;
                                if(temptype.top()=='z'){
                                    a=var_and_type(bb,"",'5',prio);
                                }
                                if(temptype.top()=='y'){
                                    a=var_and_type(bb,"",'4',prio);
                                }
                                if(temptype.top()=='h'){
                                    a=var_and_type(bb,"",'3',prio);
                                }
                                if(temptype.top()=='a'){
                                    a=var_and_type(bb,"",'2',prio);

                                }
                                if(temptype.top()=='g'){
                                    a=var_and_type(bb,"",'1',prio);

                                }
                                if(temptype.top()=='s'){
                                    a=var_and_type(bb,"",'6',prio);

                                }
                                vector<var_and_type>::iterator it;
                                if(var_list.size()==0){
                                    cout<<a.name<<"����\n";
                                    var_list.push_back(a);
                                }else{
                                   for(it=var_list.begin();it!=var_list.end();it++){
                                        if(it->name==bb&&it->priority==prio)
                                        {
                                            cout<<it->name<<endl;
                                            printf("�ظ�����\n");
                                            return;
                                        }
                                        if(it->name==bb&&it->priority>prio)
                                        {
                                            cout<<it->name<<endl;
                                            printf("�ñ�ʶ��δ����\n");
                                            return;
                                        }
                                    }
                                    cout<<a.name<<"����\n";
                                    var_list.push_back(a);
                                }
                                tempvar.pop();
                                }
                            }
                            temptype.pop();

                            break;
                        case 'X':
                            {

                            int i,j;
                            temp.push_back(":=");
                            string bb=tempvar.top();
                            if(bb=="int"){
                               temp.push_back(con_stack.top());
                                cout<<con_stack.top();
                                con_stack.pop();
                                i=temptype.top();
                                cout<<i<<'\n';
                                temptype.pop();
                                tempvar.pop();
                            }else{
                                temp.push_back(tempvar.top());
                                cout<<tempvar.top();
                                i=temptype.top();
                                cout<<i<<'\n';
                                temptype.pop();
                                tempvar.pop();
                            }

                            string ba=tempvar.top();
                            cout<<ba<<endl;
                            if(ba=="int"){
                                cout<<"���ܸ�ֵ������";
                                return;
                                /*
                                /*j=temptype.top();
                                cout<<j<<'\n';
                                cout<<con_stack.top()<<endl;
                                con_stack.pop();
                                temptype.pop();
                                tempvar.pop();*/
                            }else{
                                cout<<tempvar.top()<<endl;
                                cout<<j<<'\n';
                                j=temptype.top();
                                temptype.pop();
                                tempvar.pop();}
                            if(j==51&&(i==49||i==52||i==54)){
                                cout<<i<<'\t'<<j;
                                cout<<"���Ͳ�ƥ�䣬�޷�����";
                                return;
                            }else if(j==50&&(i==49||i>51)){
                                cout<<i<<'\t'<<j;
                                cout<<"���Ͳ�ƥ�䣬�޷�����";
                                return;
                            }else if(j==49&&(i==50||i>51)){
                                cout<<i<<'\t'<<j;
                                cout<<"���Ͳ�ƥ�䣬�޷�����";
                                return;
                            }else if(j==53&&(i==54||i<51)){
                                cout<<i<<'\t'<<j;
                                cout<<"���Ͳ�ƥ�䣬�޷�����";
                                return;
                            }else if(j==52&&(i==54||i<51)){
                                cout<<i<<'\t'<<j;
                                cout<<"���Ͳ�ƥ�䣬�޷�����";
                                return;
                            }else if(j==54&&i!=54){
                                cout<<i<<'\t'<<j;
                                cout<<"���Ͳ�ƥ�䣬�޷�����";
                                return;
                            }


                            temp.push_back("-");
                            temp.push_back(ba);
                            quaternary_list.push_back(temp);
                            break;}
                        case 'Q':
                            {
							if(len==3&&tempvar.size()>2){

                                int i,j;
                                temp.push_back(op_stack.top());
                                string bb=tempvar.top();
                                if(bb=="int"){
                                   i=temptype.top();
                                   temp.push_back(con_stack.top());
                                   cout<<con_stack.top();
                                   con_stack.pop();
                                   temptype.pop();
                                   tempvar.pop();
                                }else{temp.push_back(tempvar.top());
                                    cout<<tempvar.top();
                                    i=temptype.top();
                                   temptype.pop();
                                   tempvar.pop();}

                                string ba=tempvar.top();

                                if(ba=="int"){
                                   j=temptype.top();
                                   temp.push_back(con_stack.top());
                                   cout<<con_stack.top();
                                   con_stack.pop();
                                }else{temp.push_back(tempvar.top());
                                    cout<<tempvar.top();
                                    j=temptype.top();
                                   }
                            if(j==51&&(i==49||i==52||i==54)){
                                cout<<i<<'\t'<<j;
                                cout<<"���Ͳ�ƥ�䣬�޷�����";
                                return;
                            }else if(j==50&&(i==49||i>51)){
                                cout<<i<<'\t'<<j;
                                cout<<"���Ͳ�ƥ�䣬�޷�����";
                                return;
                            }else if(j==49&&(i==50||i>51)){
                                cout<<i<<'\t'<<j;
                                cout<<"���Ͳ�ƥ�䣬�޷�����";
                                return;
                            }else if(j==53&&(i==54||i<51)){
                                cout<<i<<'\t'<<j;
                                cout<<"���Ͳ�ƥ�䣬�޷�����";
                                return;
                            }else if(j==52&&(i==54||i<51)){
                                cout<<i<<'\t'<<j;
                                cout<<"���Ͳ�ƥ�䣬�޷�����";
                                return;
                            }else if(j==54&&i!=54){
                                cout<<i<<'\t'<<j;
                                cout<<"���Ͳ�ƥ�䣬�޷�����";
                                return;
                            }


								string abc="Temp"+to_string(var);
                                temp.push_back(abc);
                                tempvar.pop();
                                tempvar.push(abc);
                                var++;
                                quaternary_list.push_back(temp);}


                            break;}
                        case 'G':
                            {vector<var_and_type>::iterator it;
                            getline(variation,an);
                            cout<<an;
                            int fff=0;
                            for(it=var_list.begin();it!=var_list.end();it++){
                                if(it->name==an&&it->priority>prio)
                                {printf("����δ����\n");
                                    return;}
                                if(it->name==an&&it->priority<=prio){
                                     fff=1;
                                     tempvar.push(an);
                                     cout<<an<<"Y";
                                     temptype.push(it->type);
                                     break;
                                }
                            }
                            if(fff!=1){
							printf("����δ����\n");
                            return;}
                            break;

                        }

                        case 'Y':
                            {
                            cout<<"yy";
							if(sign_stack.top()=='2'){
                                vector<var_and_type>::iterator it;
								getline(variation,an);
								cout<<an;
                                for(it=var_list.begin();it!=var_list.end();it++){
                                    if(it->name==an&&it->priority>prio)
                                    {printf("����δ����\n");
                                        return;}
                                    if(it->name==an&&it->priority<=prio){

                                            tempvar.push(an);
                                            cout<<an<<"Y";
                                            temptype.push(it->type);
                                            break;
                                    }
                                }
                                if(it->name!=an){
                                    printf("����δ����\n");
                                    return;
                                }
                            }
                            if(sign_stack.top()=='3'){
                                tempvar.push("int");
                                printf("int\n");
                                getline(constant,an);
                                cout<<an;
                                con_stack.push(an);
                                string ww;
                                getline(constant,ww);
                                temptype.push(ww[0]);
                            }
                            break;}
                        case 'M':
                            {
							if(len==3&&tempvar.size()>1){
                                int i,j;
                                temp.push_back(op_stack.top());
                                op_stack.pop();
                                string bb=tempvar.top();
                                cout<<bb<<endl;
                                if(bb=="int"){
                                   i=temptype.top();
                                   temp.push_back(con_stack.top());
                                   cout<<con_stack.top()<<endl;
                                   con_stack.pop();
                                   temptype.pop();
                                   tempvar.pop();
                                }else{temp.push_back(tempvar.top());
                                    cout<<tempvar.top()<<endl;
                                    i=temptype.top();
                                   temptype.pop();
                                   tempvar.pop();}
                                string ba=tempvar.top();
                                 cout<<ba<<endl;
                                if(ba=="int"){
                                   j=temptype.top();
                                   cout<<con_stack.top()<<endl;
                                   temp.push_back(con_stack.top());
                                   con_stack.pop();
                                   temptype.pop();
                                   tempvar.pop();
                                }else{temp.push_back(tempvar.top());
                                    cout<<tempvar.top()<<endl;
                                    j=temptype.top();
                                   temptype.pop();
                                   tempvar.pop();}
                                  if(j==51&&(i==49||i==52||i==54)){
                                cout<<i<<'\t'<<j;
                                cout<<"���Ͳ�ƥ�䣬�޷�����";
                                return;
                            }else if(j==50&&(i==49||i>51)){
                                cout<<i<<'\t'<<j;
                                cout<<"���Ͳ�ƥ�䣬�޷�����";
                                return;
                            }else if(j==49&&(i==50||i>51)){
                                cout<<i<<'\t'<<j;
                                cout<<"���Ͳ�ƥ�䣬�޷�����";
                                return;
                            }else if(j==53&&(i==54||i<51)){
                                cout<<i<<'\t'<<j;
                                cout<<"���Ͳ�ƥ�䣬�޷�����";
                                return;
                            }else if(j==52&&(i==54||i<51)){
                                cout<<i<<'\t'<<j;
                                cout<<"���Ͳ�ƥ�䣬�޷�����";
                                return;
                            }else if(j==54&&i!=54){
                                cout<<i<<'\t'<<j;
                                cout<<"���Ͳ�ƥ�䣬�޷�����";
                                return;
                            }


                                stringstream aa;
								aa<<var;
								string abc="Temp"+aa.str();
								temp.push_back(abc);
                                temptype.push(min(i,j));
                                tempvar.push(abc);
                                var++;
                                quaternary_list.push_back(temp);
                            }
                            break;}
                        case 'F':
							{
							string s;
							s.push_back(sign_stack.top());
							op_stack.push(s);
                            break;}
                        case 'O':
                            {
							string s;
							s.push_back(sign_stack.top());
                            op_stack.push(s);
                            break;}
                        case 'U':
                            if(sign_stack.top()=='+'){
                                op_stack.push("+");
                            }else{op_stack.push("-");}
                            break;
                        case 'K':
                            {
                                int i=temptype.top();
                                if(i==50||i==51)
                                {
							        temp.push_back(op_stack.top()); temp.push_back("1");  temp.push_back(tempvar.top());temp.push_back(tempvar.top());
                            		quaternary_list.push_back(temp);
                            		op_stack.pop();
                            		tempvar.pop();
                            		temptype.pop();
                                    break;
                                }else{
                                    cout<<"�������Ͳ�ƥ�䣬�޷�����"<<endl;
                                    return;
                                }

                            break;}
                        case 'R':
                        	if(len>0){
                        	   string an=tempvar.top();
                        	   //�жϷ��������뺯�����������Ƿ���ͬ
                        	   char ty=temptype.top();
                        	   if(an=="int"){
                                an=con_stack.top();
                                con_stack.pop();
                        	   }
                        	   temptype.pop();
                        	   tempvar.pop();
                        	if(temptype.top()=='v'){cout<<"��������ӦΪvoid";return;}
                        	if(temptype.top()=='a'&&(ty!='2'&&ty!='3')){cout<<"��������ӦΪchar"; return;}
                            if(temptype.top()=='z'&&(ty!='5'&&ty!='3')){cout<<"��������ӦΪdouble"; return;}
                            if(temptype.top()=='y'&&(ty!='4'&&ty!='5')){cout<<"��������ӦΪfloat"; return;}
                            if(temptype.top()=='h'&&(ty!='4'&&ty!='5'&&ty!='3')){cout<<"��������ӦΪint";return;}
                            if(temptype.top()=='g'&&(ty!='1'&&ty!='3')){cout<<"��������ӦΪbool"; return;}
                            if(temptype.top()=='s'&&ty!='6'){cout<<"��������ӦΪstring"; return;}
                            temp.push_back("return"); temp.push_back("-"); temp.push_back("-"); temp.push_back(an);
                            temptype.pop();
                            quaternary_list.push_back(temp);
                            break;}
                        case 'J':
                            if(len==1){
                                int i;
                                string bb=tempvar.top();
                                string valu;
                                if(bb=="int"){
                                   temp.push_back("jnz");
                                   temp.push_back(con_stack.top());
                                   valu=con_stack.top();
                                    temp.push_back("-");
                                    con_stack.pop();
                                    i=temptype.top();

                                }else{
                                    i=temptype.top();
                                    if(i=='3'||i=='1'){
                                        temp.push_back("jnz");
                                        valu=tempvar.top();

                                        temp.push_back(tempvar.top());
                                        temp.push_back("-");
                                    }else{
                                        cout<<"���Ͳ�ƥ��";
                                        return;
                                    }

                                    }
                                    tempvar.pop();
                                    temptype.pop();
                                    temp.push_back(to_string(quaternary_list.size()+2));
                                    quaternary_list.push_back(temp);
                                    true_stack.push(quaternary_list.size());
                                    vector<string> tnnn;
                                    tnnn.push_back("jz");
                                   tnnn.push_back(valu);
                                    tnnn.push_back("-");
                                    tnnn.push_back(to_string(quaternary_list.size()));
                                    quaternary_list.push_back(tnnn);
                                    false_stack.push(quaternary_list.size());

                            }
                            if(len==2){//���������
                                int teo=true_stack.top();
                                int ueo=false_stack.top();
                                true_stack.pop();
                                quaternary_list[ueo-1][3] = to_string(ueo);
                                false_stack.pop();
                                false_stack.push(teo);
                                true_stack.push(ueo);

                            }
                            if(len==3&&tempvar.size()>1){
                                string valu;
                                string vaoc;
                                temp.push_back("j"+op_stack.top());
                                int i,j;
                                string bb=tempvar.top();
                                if(bb=="int"){
                                   i=temptype.top();
                                   temp.push_back(con_stack.top());
                                   valu=con_stack.top();
                                   con_stack.pop();
                                   temptype.pop();
                                   tempvar.pop();
                                }else{temp.push_back(tempvar.top());
                                    valu=tempvar.top();
                                    i=temptype.top();
                                   temptype.pop();
                                   tempvar.pop();}
                                if(tempvar.empty())break;
                                string ba=tempvar.top();
                                if(ba=="int"){
                                   int j=3;
                                   temp.push_back(con_stack.top());
                                    vaoc=con_stack.top();
                                   con_stack.pop();
                                   temptype.pop();
                                   tempvar.pop();
                                }else{
                                    temp.push_back(tempvar.top());
                                    vaoc=tempvar.top();
                                    j=temptype.top();
                                   tempvar.pop();
                                    temptype.pop();
                                   }
                              if(j==51&&(i==49||i==52||i==54)){
                                cout<<i<<'\t'<<j;
                                cout<<"���Ͳ�ƥ�䣬�޷�����";
                                return;
                            }else if(j==50&&(i==49||i>51)){
                                cout<<i<<'\t'<<j;
                                cout<<"���Ͳ�ƥ�䣬�޷�����";
                                return;
                            }else if(j==49&&(i==50||i>51)){
                                cout<<i<<'\t'<<j;
                                cout<<"���Ͳ�ƥ�䣬�޷�����";
                                return;
                            }else if(j==53&&(i==54||i<51)){
                                cout<<i<<'\t'<<j;
                                cout<<"���Ͳ�ƥ�䣬�޷�����";
                                return;
                            }else if(j==52&&(i==54||i<51)){
                                cout<<i<<'\t'<<j;
                                cout<<"���Ͳ�ƥ�䣬�޷�����";
                                return;
                            }else if(j==54&&i!=54){
                                cout<<i<<'\t'<<j;
                                cout<<"���Ͳ�ƥ�䣬�޷�����";
                                return;
                            }


                                    temp.push_back(to_string(quaternary_list.size()+2));
                                    quaternary_list.push_back(temp);
                                    true_stack.push(quaternary_list.size());
                                    vector<string> tnnn;
                                    tnnn.push_back("jn"+op_stack.top());
                                    op_stack.pop();
                                   tnnn.push_back(valu);
                                    tnnn.push_back(vaoc);
                                  tnnn.push_back(to_string(quaternary_list.size()));
                                    quaternary_list.push_back(tnnn);
                                   false_stack.push(quaternary_list.size());
                            }

                            break;
                        case 'H':
                            if(len==1){
                            	string s;
                            	s.push_back(sign_stack.top());
                                op_stack.push(s);
                            }
                            if(len==2){
                                string s;
                            	s.push_back(sign_stack.top());
                                sign_stack.pop();
                                state_stack.pop();
                                len--;
                                string b;
                            	b.push_back(sign_stack.top());
                                op_stack.push(b+s);
                            }
                            break;
                        case 'L':
                            {
							string s;
                            s.push_back(sign_stack.top());
                            sign_stack.pop();
                            state_stack.pop();
                            len--;
                            string b;
                            b.push_back(sign_stack.top());
                            op_stack.push(s+b);
                            break;}
                        case 'Z':
                            if(len==3){
								if(op_stack.top()=="||"){
									true_stack.pop();
									quaternary_list[true_stack.top()-1][3] = to_string(quaternary_list.size());
									int a=false_stack.top();
									false_stack.pop();
									if(quaternary_list[a-1][0]=="jnz"||quaternary_list[a-1][0].substr(0,2)!="jn")//��ǰ�����������ת����һ��
									{
									    quaternary_list[false_stack.top()-1][3] = to_string(false_stack.top()+1);

									}else{
									    quaternary_list[false_stack.top()-1][3] = to_string(false_stack.top());}
                                        false_stack.pop();
                                        false_stack.push(a);
                                    //�����һ�����תΪ��ǰsize����ת���ڶ������һ�У����㸳ֵ
                                    //�ڶ�����ת���䣬��ת��������β


                                }
                                if(op_stack.top()=="&&"){
									true_stack.pop();
									flag_false=2;
                                    //��һ����ת���䣬��ת�ȴ�����β
                                    //�ڶ�����ת���䣬��ת����β
                                }
                            }
                            break;
                        case 'E':
                            if(len>=2){
                            len-=2;
                            sign_stack.pop();
                            state_stack.pop();
                            sign_stack.pop();
                            state_stack.pop();
                            if(tempe=='}'&&sign_stack.top()=='{'){
                                //�����ת��while �жϣ� �����ת��
                                //if ��else ��ת�����������ת��һ�� �� �ȴ�����
                                //��else �����ж� �����תָ��
								temp.push_back("j");
                                temp.push_back("-");
                                temp.push_back("-");
                                temp.push_back(to_string(quaternary_list.size()+2));
								quaternary_list.push_back(temp);
								if(flag_false==2&&!false_stack.empty()){
									quaternary_list[false_stack.top()-1][3] = to_string(quaternary_list.size());
									if(!false_stack.empty()){false_stack.pop();}
                                    quaternary_list[false_stack.top()-1][3] = to_string(quaternary_list.size());
									if(!false_stack.empty()){false_stack.pop();}
									false_stack.push(quaternary_list.size());//������ת��
								}else if(!false_stack.empty()){
									quaternary_list[false_stack.top()-1][3] = to_string(quaternary_list.size());
									if(!false_stack.empty()){false_stack.pop();}
									false_stack.push(quaternary_list.size());//������ת��
								}
								flag_false=0;


                            }
							break;}

                        case 'S':
                            //������ת���� ��ע������
                            if(!false_stack.empty()){
							quaternary_list[false_stack.top()-1][3] = to_string(quaternary_list.size());}
							break;

                        case 'W':
                            //����E ������
                            if(!false_stack.empty()){
                                quaternary_list[false_stack.top()-1][3] = to_string(true_stack.top()-1);
                                false_stack.pop();
                                true_stack.pop();
                            }

							break;
						case 'V':
						    if(!false_stack.empty()){
                                false_stack.pop();
						    }
							if(!true_stack.empty()){
                                true_stack.pop();
						    }

							break;
						default:
							break;     }


                       	for(k = 0; k < len; ++k)
                       	{
                       		state_stack.pop();
//���X�������ɸ�ֵ���
//Q���мӼ��˳�����
//J �߼��������
//T �������
                       		sign_stack.pop();

                       	}

                        sign_stack.push(G[tp][0]);

                        aa=state_stack.top();
                        for(m=0;m<size_act_table[aa];++m)
                        {
                        	if(action_table[aa][m].ch==G[tp][0])
                        	{
                        		state_stack.push(action_table[aa][m].next_state);
                        		procedure_file<<action_table[aa][m].next_state<<endl;
                        	}
                        }
                        break;
                    }
            }
            }
    }
    if(!done)
    {
    	 cout << "NO" << endl;
        cout<<"����ԭ�������δ�ҵ���";
        for(i=0;i<size_act_table[work_sta];++i)
        {
        		cout<<action_table[work_sta][i].ch<<" ";
        }/*
        char p1[]="������ִ��󣬳���ԭ������ǣ�" ;
		outtextxy(600, 250, p1);
        char q1[]="ȱ�������ţ�";
        char q2[]="ȱ�������ţ�";
        char q3[]="ȱ�����Ͷ��壡";
		char q4[]="ȱ�ٱ��������壡";
		char q5[]="ȱ�ٱ������壡";
		char q6[]="ȱ��break��";
		char q7[]="ȱ��case��";
		char q8[]="ȱ�ٱ������ͣ�";
		char q9[]="ȱ��return��" ;
		char q10[]="ȱ��iostream!";
		char q11[]="ȱ��else��";
		char q12[]="ȱ��for";
		char q13[]="ȱ��if";
		char q14[]="ȱ��*";
		char q15[]="ȱ��/";
		char q16[]="ȱ��<";
		char q17[]="ȱ��>";
		char q18[]="ȱ�ٻ����ţ�";
		char q19[]="ȱ��;��";
        switch(action_table[work_sta][0].ch)
        {
        	case '(':outtextxy(600, 270, q1);
        		break;
        	case ')':outtextxy(600, 270, q2);
        		break;
        	case '+':outtextxy(600, 270, q3);
        		break;
        	case '-':outtextxy(600, 270, q3);
        		break;
        	case '=':outtextxy(600, 270, q3);
        		break;
			case '2':outtextxy(600, 270, q4);
        		break;
        	case '3':outtextxy(600, 270, q5);
        		break;
        	case 'b':outtextxy(600, 270, q6);
        		break;
        	case 'c':outtextxy(600, 270, q7);
				break;
        	case 'a':outtextxy(600, 270, q8);
        		break;
			case 'h':outtextxy(600, 270, q8);
        		break;
			case 'l':outtextxy(600, 270, q8);
        		break;
        	case 'y':outtextxy(600, 270, q8);
        		break;
        	case 'z':outtextxy(600, 270, q8);
        		break;
        	case 'r':outtextxy(600, 270, q9);
        		break;
        	case 'k':outtextxy(600, 270, q10);
        		break;
        	case 'e':outtextxy(600, 270, q11);
        		break;
        	case 'f':outtextxy(600, 270, q12);
        		break;
        	case 'i':outtextxy(600, 270, q13);
        		break;
        	case '*':outtextxy(600, 270, q14);
        		break;
        	case '/':outtextxy(600, 270, q15);
        		break;
        	case '<':outtextxy(600, 270, q16);
        		break;
        	case '>':outtextxy(600, 270, q17);
        		break;
        	case '{':outtextxy(600, 270, q18);
        		break;
        	case '}':outtextxy(600, 270, q18);
        		break;
        	case ';':outtextxy(600, 270, q19);
        		break;
		}*/
        cout<<endl;
    }
}
void init()
{
		int i,j;
		for(i=0;i<300;++i)
		{
				isV[i]=false;
		}
		for(i=0;i<300;++i)
		{
				size_item[i]=0;
		}
		for(i=0;i<300;++i)
		{
				for(j=0;j<300;++j)
				{
						first[i][j]=false;
				}
		}
		size=0;
}
void print_quaternary()
{
	for (int i = 0; i < quaternary_list.size(); i++)
	{
		cout<<i<<"("<<quaternary_list[i][0]<<','<<quaternary_list[i][1]<<','<<quaternary_list[i][2]<<','<<quaternary_list[i][3]<<")"<<endl;
		out<<i<<"("<<quaternary_list[i][0]<<','<<quaternary_list[i][1]<<','<<quaternary_list[i][2]<<','<<quaternary_list[i][3]<<")"<<endl;
	}
}
char lookup(string s){
    vector<var_and_type>::iterator it;
    for(it=var_list.begin();it!=var_list.end();it++){
        if(it->name==s){
            return it->type;
        }
    }
    return 0;
}
string findup(string s){
    vector<var_and_type>::iterator it;
    for(it=var_list.begin();it!=var_list.end();it++){
        if(it->name==s){
            return it->data;
        }
    }
    return "";
}
void andlist(string s,string data){
    vector<var_and_type>::iterator it;
    for(it=var_list.begin();it!=var_list.end();it++){
        if(it->name==s){
            it->data=data;
            return;
        }
    }
}
int Is_constant(string a)
{
	int len=a.size();
	int flag=1;
	int w=1;
	if(a=="true"||a=="false")return 1;
	for(int j=0;j<len;++j)
	{
		if(isdigit(a[j])&&(flag==1||flag==2||flag==3||flag==4||flag==5))
		{
		    if(a[j]==0&&j==0){flag=8;w=3;}
		    if(flag==1){
                w=3;
		    }
		    if(flag==2){
                w=w>4?w:4;
                flag=5;//ΪС��
		    }
		    if(flag==3){
                w=5;
                flag=1;
		    }
		    if(flag==4){
                w=5;
                flag=1;
		    }

		}else if(a[j]=='.'&&(flag==1||flag==8)){
		    if(j==len-1||j==0){
                cout<<"�Ƿ�����"<<endl;
                return 0;
		    }
			w=w>4?w:4;
			flag=2;
		}else if(a[j]=='e'&&(flag==1||flag==5)){
			if(j==len-1||j==0) return 0;
			w=5;
			flag=3;
		}else if((a[j]=='+'||a[j]=='-')&&(flag==1||flag==3||flag==5)){
			if(j==len-1) return 0;
			if(a[j]=='+'&&j==0)return 0;
			w=5;
			flag=4;
		}else if(a[j]=='i'&&(flag==1||flag==5)){
			if(j!=len-1) return 0;
			w=5;
			flag=1;
		}else if(a[j]=='f'&&flag==5){
			if(j!=len-1) return 0;
			if(j==len-1&&w!=4) return 0;
		}else{
		    return 0;
		}

	}
	if(w==4&&a[len-1]!='f') w=5;
	if(flag==1||flag==5||flag==8) return w;
	else return 0;
}
stack<int> in_va;
stack<string> str_va;
void explanation()
{
    int type;
    string anoc;
	for (int i = 2; i < quaternary_list.size(); i++)
	{
		if(quaternary_list[i][0]==":="){//��ֵ���
		    int as=lookup(quaternary_list[i][3]);
             if(quaternary_list[i][1].substr(0,4)=="Temp"){//��ʱ������ֵ
                int as=lookup(quaternary_list[i][3]);
                string an=str_va.top();
                int www=in_va.top();
                str_va.pop();
                in_va.pop();
                if(as==49){
                    if(an=="true"||an=="false"){
                       explain<<quaternary_list[i][3]<<"="<<an<<endl;
                    }else if(atoi(an.c_str())>0){
                        explain<<quaternary_list[i][3]<<"="<<"true"<<endl;
                        an="true";
                    }else{
                        explain<<quaternary_list[i][3]<<"="<<"false"<<endl;
                        an="false";
                    }
                    //
                }else if(as==50){
                    if(www==2){
                        explain<<quaternary_list[i][3]<<"="<<an<<endl;
                    }else if(www==3){
                        char ans=atoi(an.c_str());
                        explain<<quaternary_list[i][3]<<"="<<ans<<endl;
                    } {cout<<"����";return;}

                    //
                }else if(as==51){
                    if(www>3){
                        int k;
                        for(k=0;i<quaternary_list[k][1].size();k++){
                            if(quaternary_list[i][1][k]=='.')break;
                        }
                        an=quaternary_list[i][1].substr(0,k+1);
                    }
                    explain<<quaternary_list[i][3]<<"="<<an<<endl;
                    //
                }else if(as==52){
                    explain<<quaternary_list[i][3]<<"="<<an<<endl;
                    //
                }else if(as==53){
                    //
                    explain<<quaternary_list[i][3]<<"="<<an<<endl;
                }else{
                    explain<<quaternary_list[i][3]<<"="<<an<<endl;
                }
                andlist(quaternary_list[i][3],an);

            }else if(findup(quaternary_list[i][1])!=""){//������ֵ������
                string an;
                an=findup(quaternary_list[i][1]);
                int www=lookup(quaternary_list[i][1]);
                www-=48;
                int as=lookup(quaternary_list[i][3]);
                if(as==49){
                    if(an=="true"||an=="false"){
                       explain<<quaternary_list[i][3]<<"="<<an<<endl;
                    }else if(atoi(an.c_str())>0){
                        explain<<quaternary_list[i][3]<<"="<<"true"<<endl;
                        an="true";
                    }else{
                        explain<<quaternary_list[i][3]<<"="<<"false"<<endl;
                        an="false";
                    }
                    //
                }else if(as==50){
                    if(www==2){
                        explain<<quaternary_list[i][3]<<"="<<an<<endl;
                    }else if(www==3){
                        char ans=atoi(an.c_str());
                        explain<<quaternary_list[i][3]<<"="<<ans<<endl;
                    } {cout<<"����";return;}

                    //
                }else if(as==51){
                    if(www>3){
                        int k;
                        for(k=0;i<quaternary_list[k][1].size();k++){
                            if(quaternary_list[i][1][k]=='.')break;
                        }
                        an=quaternary_list[i][1].substr(0,k+1);
                    }
                    explain<<quaternary_list[i][3]<<"="<<an<<endl;
                    //
                }else if(as==52){
                    explain<<quaternary_list[i][3]<<"="<<an<<endl;
                    //
                }else if(as==53){
                    //
                    explain<<quaternary_list[i][3]<<"="<<an<<endl;
                }else{
                    explain<<quaternary_list[i][3]<<"="<<an<<endl;
                }
                andlist(quaternary_list[i][3],an);
            }else {//�������ֵ���ǳ���
                int w=Is_constant(quaternary_list[i][1]);
                anoc=quaternary_list[i][1];
                if(as==49){
                    if(anoc=="true"||anoc=="false"){
                       explain<<quaternary_list[i][3]<<"="<<anoc<<endl;
                       cout<<quaternary_list[i][3]<<"="<<anoc;
                    }else if(atoi(anoc.c_str())>0){
                        explain<<quaternary_list[i][3]<<"="<<"true"<<endl;
                        cout<<quaternary_list[i][3]<<"="<<"true";
                        anoc="true";
                    }else{
                        explain<<quaternary_list[i][3]<<"="<<"false"<<endl;
                        anoc="false";
                    }
                    //
                }else if(as==50){
                    if(w==2){
                        explain<<quaternary_list[i][3]<<"="<<anoc<<endl;
                    }else {cout<<"����";return;}

                    //
                }else if(as==51){
                    int c=Is_constant(quaternary_list[i][1]);
                    if(c>3){
                        int k;
                        for(k=0;i<quaternary_list[k][1].size();k++){
                            if(quaternary_list[i][1][k]=='.')break;
                        }
                        anoc=quaternary_list[i][1].substr(0,k+1);
                    }
                    explain<<quaternary_list[i][3]<<"="<<anoc<<endl;
                    cout<<quaternary_list[i][3]<<"="<<anoc;
                    //
                }else if(as==52){
                    explain<<quaternary_list[i][3]<<"="<<anoc<<endl;
                    //
                }else if(as==53){
                    //
                    explain<<quaternary_list[i][3]<<"="<<anoc<<endl;
                }else{
                    explain<<quaternary_list[i][3]<<"="<<anoc<<endl;
                }
                andlist(quaternary_list[i][3],anoc);
            }


		}else if(!isalpha(quaternary_list[i][0][0])){//+-����
		    if(quaternary_list[i][0][0]=='*'){
                //������߾�Ϊ������������
                string ac,ad;
                int www=0;
                string an;
                if(quaternary_list[i][2].substr(0,4)=="Temp"){
                    www=in_va.top();
                    ac=str_va.top();
                    str_va.pop();
                    in_va.pop();
                }else if(findup(quaternary_list[i][2])!=""){
                        an=findup(quaternary_list[i][2]);
                        www=lookup(quaternary_list[i][2]);
                        www-=48;
                        ac=an;
                }else{
                    ac=quaternary_list[i][2];
                    www=Is_constant(quaternary_list[i][2]);
                }

                string an1;
                int www1=0;
                if(quaternary_list[i][1].substr(0,4)=="Temp"){
                    www1=in_va.top();
                    ad=str_va.top();
                    str_va.pop();
                    in_va.pop();
                }else if(findup(quaternary_list[i][1])!=""){
                        an1=findup(quaternary_list[i][1]);
                        www1=lookup(quaternary_list[i][1]);
                        www1-=48;
                        ad=an1;
                }else{
                        www1=Is_constant(quaternary_list[i][1]);
                        ad=quaternary_list[i][1];
                    }
                if(www1==3&&www==3){
                    int ww=atoi(ac.c_str())*atoi(ad.c_str());
                    str_va.push(to_string(ww));
                    in_va.push(3);

                }else if(www==3&&(www1==4||www1==5)){
                    double ww=atoi(ac.c_str())*atof(ad.c_str());
                    str_va.push(to_string(ww));
                    in_va.push(www1);

                }else if((www==4||www==5)&&www1==3){
                    double ww=atof(ac.c_str())*atoi(ad.c_str());
                    str_va.push(to_string(ww));
                    in_va.push(www);

                }else if((www==4||www==5)&&(www1==4||www1==5)){
                    double ww=atof(ac.c_str())*atof(ad.c_str());
                    str_va.push(to_string(ww));
                    in_va.push(max(www,www1));

                }else{
                    cout<<"���ַ����Ͳ�֧�ֳ˷�";
                    return;
                }


		    }else if(quaternary_list[i][0][0]=='/'){
                string ac,ad;
                int www=0;
                string an;
                if(quaternary_list[i][2].substr(0,4)=="Temp"){
                    www=in_va.top();
                    ac=str_va.top();
                    str_va.pop();
                    in_va.pop();
                }else if(findup(quaternary_list[i][2])!=""){
                        an=findup(quaternary_list[i][2]);
                        www=lookup(quaternary_list[i][2]);
                        www-=48;
                        ac=an;
                }else{
                    ac=quaternary_list[i][2];
                    www=Is_constant(quaternary_list[i][2]);
                }

                string an1;
                int www1=0;
                if(quaternary_list[i][1].substr(0,4)=="Temp"){
                    www1=in_va.top();
                    ad=str_va.top();
                    str_va.pop();
                    in_va.pop();
                }else if(findup(quaternary_list[i][1])!=""){
                        an1=findup(quaternary_list[i][1]);
                        www1=lookup(quaternary_list[i][1]);
                        www1-=48;
                        ad=an1;
                }else{
                        www1=Is_constant(quaternary_list[i][1]);
                        ad=quaternary_list[i][1];
                    }

                if(atoi(ad.c_str())==0){cout<<"��������Ϊ0";return;}
                if(www1==3&&www==3){
                    int ww=atoi(ac.c_str())/atoi(ad.c_str());
                    str_va.push(to_string(ww));
                    in_va.push(3);

                }else if(www==3&&(www1==4||www1==5)){
                    double ww=atoi(ac.c_str())/atof(ad.c_str());
                    str_va.push(to_string(ww));
                    in_va.push(www1);

                }else if((www==4||www==5)&&www1==3){
                    double ww=atof(ac.c_str())/atoi(ad.c_str());
                    str_va.push(to_string(ww));
                    in_va.push(www);

                }else if((www==4||www==5)&&(www1==4||www1==5)){
                    double ww=atof(ac.c_str())/atof(ad.c_str());
                    str_va.push(to_string(ww));
                    in_va.push(max(www,www1));

                }else{
                    cout<<"���ַ����Ͳ�֧�ֳ���";
                    return;
                }

		    }else if(quaternary_list[i][0][0]=='-'){
                string ac,ad;
                int www=0;
                string an;
                if(quaternary_list[i][2].substr(0,4)=="Temp"){
                    www=in_va.top();
                    ac=str_va.top();
                    str_va.pop();
                    in_va.pop();
                }else if(findup(quaternary_list[i][2])!=""){
                        an=findup(quaternary_list[i][2]);
                        www=lookup(quaternary_list[i][2]);
                        www-=48;
                        ac=an;
                }else{
                    ac=quaternary_list[i][2];
                    www=Is_constant(quaternary_list[i][2]);
                }

                string an1;
                int www1=0;
                if(quaternary_list[i][1].substr(0,4)=="Temp"){
                    www1=in_va.top();
                    ad=str_va.top();
                    str_va.pop();
                    in_va.pop();
                }else if(findup(quaternary_list[i][1])!=""){
                        an1=findup(quaternary_list[i][1]);
                        www1=lookup(quaternary_list[i][1]);
                        www1-=48;
                        ad=an1;
                }else{
                        www1=Is_constant(quaternary_list[i][1]);
                        ad=quaternary_list[i][1];
                    }

                if(www1==3&&www==3){
                    int ww=atoi(ac.c_str())-atoi(ad.c_str());
                    str_va.push(to_string(ww));
                    in_va.push(3);

                }else if(www==3&&(www1==4||www1==5)){
                    double ww=atoi(ac.c_str())-atof(ad.c_str());
                    str_va.push(to_string(ww));
                    in_va.push(www1);

                }else if((www==4||www==5)&&www1==3){
                    double ww=atof(ac.c_str())-atoi(ad.c_str());
                    str_va.push(to_string(ww));
                    in_va.push(www);

                }else if((www==4||www==5)&&(www1==4||www1==5)){
                    double ww=atof(ac.c_str())-atof(ad.c_str());
                    str_va.push(to_string(ww));
                    in_va.push(max(www,www1));

                }else{
                    cout<<"���ַ����Ͳ�֧�ּ���";
                    return;
                }

		    }else if(quaternary_list[i][0][0]=='+'){
                string ac,ad;
                int www=0;
                string an;
                if(quaternary_list[i][2].substr(0,4)=="Temp"){
                    www=in_va.top();
                    ac=str_va.top();
                    str_va.pop();
                    in_va.pop();
                }else if(findup(quaternary_list[i][2])!=""){
                        an=findup(quaternary_list[i][2]);
                        www=lookup(quaternary_list[i][2]);
                        www-=48;
                        ac=an;
                }else{
                    ac=quaternary_list[i][2];
                    www=Is_constant(quaternary_list[i][2]);
                }

                string an1;
                int www1=0;
                if(quaternary_list[i][1].substr(0,4)=="Temp"){
                    www1=in_va.top();
                    ad=str_va.top();
                    str_va.pop();
                    in_va.pop();
                }else if(findup(quaternary_list[i][1])!=""){
                        an1=findup(quaternary_list[i][1]);
                        www1=lookup(quaternary_list[i][1]);
                        www1-=48;
                        ad=an1;
                }else{
                        www1=Is_constant(quaternary_list[i][1]);
                        ad=quaternary_list[i][1];
                    }
                if(www1==3&&www==3){
                    int ww=atoi(ac.c_str())+atoi(ad.c_str());
                    str_va.push(to_string(ww));
                    in_va.push(3);

                }else if(www==3&&(www1==4||www1==5)){
                    double ww=atoi(ac.c_str())+atof(ad.c_str());
                    str_va.push(to_string(ww));
                    in_va.push(www1);

                }else if((www==4||www==5)&&www1==3){
                    double ww=atof(ac.c_str())+atoi(ad.c_str());
                    str_va.push(to_string(ww));
                    in_va.push(www);

                }else if((www==4||www==5)&&(www1==4||www1==5)){
                    double ww=atof(ac.c_str())+atof(ad.c_str());
                    str_va.push(to_string(ww));
                    in_va.push(max(www,www1));

                }else if(www==6||www1==6||lookup(quaternary_list[i][3])=='6'){
                    string ww=ac+ad;
                    /*int z=ac.size()+ad.size();
                    for(int wn=0;wn<z;wn++){
                        if(wn<ac.size()){
                            ww[wn]=ac[wn];
                        }else{
                            ww[wn]=ad[wn];
                        }
                    }
                    ww[z]='\0';*/
                    str_va.push(ww);
                    in_va.push(6);
                }else{
                    cout<<"���ַ����Ͳ�֧�ּӷ�";
                    return;
                }

		    }
		    if(quaternary_list[i][3].substr(0,4)=="Temp"){
                continue;
		    }else{
		        andlist(quaternary_list[i][3],str_va.top());
		        explain<<quaternary_list[i][3]<<"="<<str_va.top()<<endl;
		        str_va.pop();
		        in_va.pop();
		    }

		}else if(quaternary_list[i][0]=="j"){
		    i=atoi(quaternary_list[i][3].c_str())-1;
		}else if(quaternary_list[i][0]=="return"){
		    explain<<quaternary_list[i][0]<<" "<<quaternary_list[i][3]<<endl;
		}else if(quaternary_list[i][0][0]=='j'){
		     if(quaternary_list[i][0][1]=='n'){
                    int len=quaternary_list[i][0].size();
                    string aoc=quaternary_list[i][0].substr(2,len-2);
                    if(aoc==">=")
                    {
                        string ab;
                        string ac;
                        string an;
                        an=quaternary_list[i][2];
                        ac=quaternary_list[i][1];
                        if(Is_constant(an)){
                            if(Is_constant(ac)){

                            }else if(ac.substr(0,4)=="Temp"){
                                ac=str_va.top();
                            }else{
                                ac=findup(quaternary_list[i][1]);
                            }
                            if(an<ac) i=atoi(quaternary_list[i][3].c_str())-1;
                            else continue;
                        }else if(an.substr(0,4)=="Temp"){
                            an=str_va.top();
                             if(Is_constant(ac)){

                            }else{
                                ac=findup(quaternary_list[i][1]);
                            }
                            if(an<ac) i=atoi(quaternary_list[i][3].c_str())-1;
                            else continue;

                        }else{
                            string an=findup(quaternary_list[i][2]);
                            if(Is_constant(ac)){

                            }else if(ac.substr(0,4)=="Temp"){
                                ac=str_va.top();
                            }else{
                                ac=findup(quaternary_list[i][1]);
                            }
                            if(an<ac) i=atoi(quaternary_list[i][3].c_str())-1;
                            else continue;
                        }
                   }
                   else if(aoc=="<=")
                   {
                        string ab;
                        string ac;
                        string an;
                        an=quaternary_list[i][2];
                        ac=quaternary_list[i][1];
                        if(Is_constant(an)){
                            if(Is_constant(ac)){

                            }else if(ac.substr(0,4)=="Temp"){
                                ac=str_va.top();
                            }else{
                                ac=findup(quaternary_list[i][1]);
                            }
                            if(an>ac) i=atoi(quaternary_list[i][3].c_str())-1;
                            else continue;
                        }else if(an.substr(0,4)=="Temp"){
                            an=str_va.top();
                             if(Is_constant(ac)){

                            }else{
                                ac=findup(quaternary_list[i][1]);
                            }
                            if(an>ac) i=atoi(quaternary_list[i][3].c_str())-1;
                            else continue;

                        }else{
                            string an=findup(quaternary_list[i][2]);
                            if(Is_constant(ac)){

                            }else if(ac.substr(0,4)=="Temp"){
                                ac=str_va.top();
                            }else{
                                ac=findup(quaternary_list[i][1]);
                            }
                            if(an>ac) i=atoi(quaternary_list[i][3].c_str())-1;
                            else continue;
                        }
                   }
                   else if(aoc=="==")
                   {
                        string ab;
                        string ac;
                        string an;
                        an=quaternary_list[i][2];
                        ac=quaternary_list[i][1];
                        if(Is_constant(an)){
                            if(Is_constant(ac)){

                            }else if(ac.substr(0,4)=="Temp"){
                                ac=str_va.top();
                            }else{
                                ac=findup(quaternary_list[i][1]);
                            }
                            if(an!=ac) i=atoi(quaternary_list[i][3].c_str())-1;
                            else continue;
                        }else if(an.substr(0,4)=="Temp"){
                            an=str_va.top();
                             if(Is_constant(ac)){

                            }else{
                                ac=findup(quaternary_list[i][1]);
                            }
                            if(an!=ac) i=atoi(quaternary_list[i][3].c_str())-1;
                            else continue;

                        }else{
                            string an=findup(quaternary_list[i][2]);
                            if(Is_constant(ac)){

                            }else if(ac.substr(0,4)=="Temp"){
                                ac=str_va.top();
                            }else{
                                ac=findup(quaternary_list[i][1]);
                            }
                            if(an!=ac) i=atoi(quaternary_list[i][3].c_str())-1;
                            else continue;
                        }
                   }
                   else if(aoc=="!=")
                   {
                        string ab;
                        string ac;
                        string an;
                        an=quaternary_list[i][2];
                        ac=quaternary_list[i][1];
                        if(Is_constant(an)){
                            if(Is_constant(ac)){

                            }else if(ac.substr(0,4)=="Temp"){
                                ac=str_va.top();
                            }else{
                                ac=findup(quaternary_list[i][1]);
                            }
                            if(an==ac) i=atoi(quaternary_list[i][3].c_str())-1;
                            else continue;
                        }else if(an.substr(0,4)=="Temp"){
                            an=str_va.top();
                             if(Is_constant(ac)){

                            }else{
                                ac=findup(quaternary_list[i][1]);
                            }
                            if(an==ac) i=atoi(quaternary_list[i][3].c_str())-1;
                            else continue;

                        }else{
                            string an=findup(quaternary_list[i][2]);
                            if(Is_constant(ac)){

                            }else if(ac.substr(0,4)=="Temp"){
                                ac=str_va.top();
                            }else{
                                ac=findup(quaternary_list[i][1]);
                            }
                            if(an==ac) i=atoi(quaternary_list[i][3].c_str())-1;
                            else continue;
                        }
                   }
                   else if(aoc=="<")
                   {
                         string ab;
                        string ac;
                        string an;
                        an=quaternary_list[i][2];
                        ac=quaternary_list[i][1];
                        if(Is_constant(an)){
                            if(Is_constant(ac)){

                            }else if(ac.substr(0,4)=="Temp"){
                                ac=str_va.top();
                            }else{
                                ac=findup(quaternary_list[i][1]);
                            }
                            if(an==ac||an>ac) i=atoi(quaternary_list[i][3].c_str())-1;
                            else continue;
                        }else if(an.substr(0,4)=="Temp"){
                            an=str_va.top();
                             if(Is_constant(ac)){

                            }else{
                                ac=findup(quaternary_list[i][1]);
                            }
                            if(an==ac||an>ac) i=atoi(quaternary_list[i][3].c_str())-1;
                            else continue;

                        }else{
                            string an=findup(quaternary_list[i][2]);
                            if(Is_constant(ac)){

                            }else if(ac.substr(0,4)=="Temp"){
                                ac=str_va.top();
                            }else{
                                ac=findup(quaternary_list[i][1]);
                            }
                            if(an==ac) i=atoi(quaternary_list[i][3].c_str())-1;
                            else continue;
                        }
                    }
                    else if(aoc==">")
                    {
                        string ab;
                        string ac;
                        string an;
                        an=quaternary_list[i][2];
                        ac=quaternary_list[i][1];
                        if(Is_constant(an)){
                            if(Is_constant(ac)){

                            }else if(ac.substr(0,4)=="Temp"){
                                ac=str_va.top();
                            }else{
                                ac=findup(quaternary_list[i][1]);
                            }
                            if(an==ac||an<ac) i=atoi(quaternary_list[i][3].c_str())-1;
                            else continue;
                        }else if(an.substr(0,4)=="Temp"){
                            an=str_va.top();
                             if(Is_constant(ac)){

                            }else{
                                ac=findup(quaternary_list[i][1]);
                            }
                            if(an==ac||an<ac) i=atoi(quaternary_list[i][3].c_str())-1;
                            else continue;

                        }else{
                            string an=findup(quaternary_list[i][2]);
                            if(Is_constant(ac)){

                            }else if(ac.substr(0,4)=="Temp"){
                                ac=str_va.top();
                            }else{
                                ac=findup(quaternary_list[i][1]);
                            }
                            if(an==ac||an<ac) i=atoi(quaternary_list[i][3].c_str())-1;
                            else continue;
                        }
                    }
                    else if(aoc=="z")
                    {
                        string an;
                        string ab;
                        an=quaternary_list[i][1];
                        if(Is_constant(an)){
                            if(an=="0"||an=="false"){
                                continue;
                            }else{
                                i=atoi(quaternary_list[i][3].c_str())-1;
                            }
                        }else{
                            string aw=findup(quaternary_list[i][1]);
                            if(aw=="0"||aw=="false"){
                                continue;
                            }else{
                                i=atoi(quaternary_list[i][3].c_str())-1;
                            }
                        }
                    }
		     }else{
                    int len=quaternary_list[i][0].size();
                    string aoc=quaternary_list[i][0].substr(1,len-1);
                    if(aoc==">="){
                        string ab;
                        string ac;
                        string an;
                        an=quaternary_list[i][2];
                        ac=quaternary_list[i][1];
                        if(Is_constant(an)){
                            if(Is_constant(ac)){

                            }else if(ac.substr(0,4)=="Temp"){
                                ac=str_va.top();
                            }else{
                                ac=findup(quaternary_list[i][1]);
                            }
                            if(an==ac||an>ac) i=atoi(quaternary_list[i][3].c_str())-1;
                            else continue;
                        }else if(an.substr(0,4)=="Temp"){
                            an=str_va.top();
                             if(Is_constant(ac)){

                            }else{
                                ac=findup(quaternary_list[i][1]);
                            }
                            if(an==ac||an>ac) i=atoi(quaternary_list[i][3].c_str())-1;
                            else continue;

                        }else{
                            string an=findup(quaternary_list[i][2]);
                            if(Is_constant(ac)){

                            }else if(ac.substr(0,4)=="Temp"){
                                ac=str_va.top();
                            }else{
                                ac=findup(quaternary_list[i][1]);
                            }
                            if(an==ac||an>ac) i=atoi(quaternary_list[i][3].c_str())-1;
                            else continue;
                        }
                  } else if(aoc=="<="){
                        string ab;
                        string ac;
                        string an;
                        an=quaternary_list[i][2];
                        ac=quaternary_list[i][1];
                        if(Is_constant(an)){
                            if(Is_constant(ac)){

                            }else if(ac.substr(0,4)=="Temp"){
                                ac=str_va.top();
                            }else{
                                ac=findup(quaternary_list[i][1]);
                            }
                            if(an==ac||an<ac) i=atoi(quaternary_list[i][3].c_str())-1;
                            else continue;
                        }else if(an.substr(0,4)=="Temp"){
                            an=str_va.top();
                             if(Is_constant(ac)){

                            }else{
                                ac=findup(quaternary_list[i][1]);
                            }
                            if(an==ac||an<ac) i=atoi(quaternary_list[i][3].c_str())-1;
                            else continue;

                        }else{
                            string an=findup(quaternary_list[i][2]);
                            if(Is_constant(ac)){

                            }else if(ac.substr(0,4)=="Temp"){
                                ac=str_va.top();
                            }else{
                                ac=findup(quaternary_list[i][1]);
                            }
                            if(an==ac||an<ac) i=atoi(quaternary_list[i][3].c_str())-1;
                            else continue;
                        }
                     }else if(aoc=="=="){
                        string ab;
                        string ac;
                        string an;
                        an=quaternary_list[i][2];
                        ac=quaternary_list[i][1];
                        if(Is_constant(an)){
                            if(Is_constant(ac)){

                            }else if(ac.substr(0,4)=="Temp"){
                                ac=str_va.top();
                            }else{
                                ac=findup(quaternary_list[i][1]);
                            }
                            if(an==ac) i=atoi(quaternary_list[i][3].c_str())-1;
                            else continue;
                        }else if(an.substr(0,4)=="Temp"){
                            an=str_va.top();
                             if(Is_constant(ac)){

                            }else{
                                ac=findup(quaternary_list[i][1]);
                            }
                            if(an==ac) i=atoi(quaternary_list[i][3].c_str())-1;
                            else continue;

                        }else{
                            string an=findup(quaternary_list[i][2]);
                            if(Is_constant(ac)){

                            }else if(ac.substr(0,4)=="Temp"){
                                ac=str_va.top();
                            }else{
                                ac=findup(quaternary_list[i][1]);
                            }
                            if(an==ac) i=atoi(quaternary_list[i][3].c_str())-1;
                            else continue;
                        }
                    }else if(aoc=="!="){
                         string ab;
                        string ac;
                        string an;
                        an=quaternary_list[i][2];
                        ac=quaternary_list[i][1];
                        if(Is_constant(an)){
                            if(Is_constant(ac)){

                            }else if(ac.substr(0,4)=="Temp"){
                                ac=str_va.top();
                            }else{
                                ac=findup(quaternary_list[i][1]);
                            }
                            if(an!=ac)i=atoi(quaternary_list[i][3].c_str())-1;
                            else continue;
                        }else if(an.substr(0,4)=="Temp"){
                            an=str_va.top();
                             if(Is_constant(ac)){

                            }else{
                                ac=findup(quaternary_list[i][1]);
                            }
                            if(an!=ac) i=atoi(quaternary_list[i][3].c_str())-1;
                            else continue;

                        }else{
                            string an=findup(quaternary_list[i][2]);
                            if(Is_constant(ac)){

                            }else if(ac.substr(0,4)=="Temp"){
                                ac=str_va.top();
                            }else{
                                ac=findup(quaternary_list[i][1]);
                            }
                            if(an!=ac) i=atoi(quaternary_list[i][3].c_str())-1;
                            else continue;
                        }
                     }else if(aoc==">"){
                       string ab;
                        string ac;
                        string an;
                        an=quaternary_list[i][2];
                        ac=quaternary_list[i][1];
                        if(Is_constant(an)){
                            if(Is_constant(ac)){

                            }else if(ac.substr(0,4)=="Temp"){
                                ac=str_va.top();
                            }else{
                                ac=findup(quaternary_list[i][1]);
                            }
                            if(an>ac) i=atoi(quaternary_list[i][3].c_str())-1;
                            else continue;
                        }else if(an.substr(0,4)=="Temp"){
                            an=str_va.top();
                             if(Is_constant(ac)){

                            }else{
                                ac=findup(quaternary_list[i][1]);
                            }
                            if(an>ac) i=atoi(quaternary_list[i][3].c_str())-1;
                            else continue;

                        }else{
                            string an=findup(quaternary_list[i][2]);
                            if(Is_constant(ac)){

                            }else if(ac.substr(0,4)=="Temp"){
                                ac=str_va.top();
                            }else{
                                ac=findup(quaternary_list[i][1]);
                            }
                            if(an>ac) i=atoi(quaternary_list[i][3].c_str())-1;
                            else continue;
                        }

                    }else if(aoc=="<"){
                        string ab;
                        string ac;
                        string an;
                        an=quaternary_list[i][2];
                        ac=quaternary_list[i][1];
                        if(Is_constant(an)){
                            if(Is_constant(ac)){

                            }else if(ac.substr(0,4)=="Temp"){
                                ac=str_va.top();
                            }else{
                                ac=findup(quaternary_list[i][1]);
                            }
                            if(an<ac)i=atoi(quaternary_list[i][3].c_str())-1;
                            else continue;
                        }else if(an.substr(0,4)=="Temp"){
                            an=str_va.top();
                             if(Is_constant(ac)){

                            }else{
                                ac=findup(quaternary_list[i][1]);
                            }
                            if(an<ac)i=atoi(quaternary_list[i][3].c_str())-1;
                            else continue;

                        }else{
                            string an=findup(quaternary_list[i][2]);
                            if(Is_constant(ac)){

                            }else if(ac.substr(0,4)=="Temp"){
                                ac=str_va.top();
                            }else{
                                ac=findup(quaternary_list[i][1]);
                            }
                            if(an<ac) i=atoi(quaternary_list[i][3].c_str())-1;
                            else continue;
                        }

                    }else if(aoc=="z"){
                        string an;
                        string ab;
                        an=quaternary_list[i][1];
                        if(Is_constant(an)){
                            if(an!="0"||an=="false"){
                                continue;
                            }else{
                                i=atoi(quaternary_list[i][3].c_str())-1;
                            }
                        }else{
                            string aw=findup(quaternary_list[i][1]);
                            if(aw!="0"||aw=="false"){
                                continue;
                            }else{
                               i=atoi(quaternary_list[i][3].c_str())-1;
                            }
                        }
                    }
		     }


		}

	}

}

void open_file()
{
	grammar_file.open("�﷨����_�ķ�.txt");
	out.open("��Ԫʽ.txt");
    input_file.open("output.txt");
    items_file.open("��Ŀ��.txt");
    action_file.open("������.txt");
    firstset_file.open("first��.txt");
    procedure_file.open("��������.txt");
	constant.open("constant.txt");
	variation.open("variation.txt");
	explain.open("explain.txt");

}
void LR1()
{
	get_grammar();
    get_first();
    write_first_set();
    make_set();
    get_action();
    judge();
}
void close_file()
{
	grammar_file.close();
    input_file.close();
    items_file.close();
    action_file.close();
    firstset_file.close();
    procedure_file.close();
	constant.close();
	variation.close();
	out.close();
}
int main()
{
    init();
    open_file();
    LR1();
    print_quaternary();
    close_file();
    explanation();
    explain.close();
    return 0;
}
}
/*/**********************************************/
namespace stu{
const int num_of_keyword=23;
const int num_of_MO=20;
const int num_of_BO=20;
const int num_of_D=20;
const char keyword[50][12]={"break","case","char","continue","do","default","double",
"else","float","for","if","int","include","long long","main","return","string","typedef","void","unsigned","while","iostream","bool"};
const char Monocular_Operator[20]={'+','-','*','/','!','%','~','&','|','^','=','>','<'};   //��Ŀ�����
const char Binocular_Operator[20][5]={"++","--","&&","||","<=","!=","==",">=","+=","-=","*=","/="}; //˫Ŀ�����
const char Delimiter[20]={',','(',')','{','}',';','<','>','#','[',']'}; //���
FILE* file_source=NULL;
ifstream input;
ofstream output;
ofstream constant;
ofstream variation;
/******************************************/
//�ؼ���    1
//��ʶ��    2
//����		3
//�����	4
//���		5
/******************************************/
char f(char str[])        //ӳ�䵽һ���ַ�����ʾ
{
	if(strcmp(str,keyword[0])==0)
		return 'b';
	if(strcmp(str,keyword[1])==0)
		return 'c';
	if(strcmp(str,keyword[2])==0)   //char  a
		return 'a';
	if(strcmp(str,keyword[3])==0)   //continue   o
		return 'o';
	if(strcmp(str,keyword[4])==0)//do
		return 'd';
	if(strcmp(str,keyword[5])==0)	//default    n
		return 'n';
	if(strcmp(str,keyword[6])==0)	//double   z
		return 'z';
	if(strcmp(str,keyword[7])==0) //else
		return 'e';
	if(strcmp(str,keyword[8])==0)	//float  y
		return 'y';
	if(strcmp(str,keyword[9])==0) //for
		return 'f';
	if(strcmp(str,keyword[10])==0) //if
		return 'i';
	if(strcmp(str,keyword[11])==0)  //int    h
		return 'h';
	if(strcmp(str,keyword[12])==0)	//include  p
		return 'p';
	if(strcmp(str,keyword[13])==0) //long long
		return 'l';
	if(strcmp(str,keyword[14])==0) //main
		return 'm';
	if(strcmp(str,keyword[15])==0) //return
		return 'r';
	if(strcmp(str,keyword[16])==0)//string s
		return 's';
	if(strcmp(str,keyword[17])==0) //typedef
		return 't';
	if(strcmp(str,keyword[18])==0)// void
		return 'v';
	if(strcmp(str,keyword[19])==0) //unsigned
		return 'u';
	if(strcmp(str,keyword[20])==0) //while
		return 'w';
	if(strcmp(str,keyword[21])==0)     //iostream   k
		return 'k';
    if(strcmp(str,keyword[22])==0)     //bool   g
		return 'g';
}

char state[100];
int len_state;
//char move[100][100];
char start;
char final[100];
int len_final;
bool is_final[150];

struct NFA_set
{
	char set[100];
	int len=0;
};
char buffer[100];
int buffer_size=0;

NFA_set movel[100][100];

char N_state[100];
int N_len_state;
char N_start;
char N_final[100];
int N_len_final;
bool N_is_final[100];

NFA_set new_set[100];
int num_new_set=0;
int dfa[150][150];

bool IsInteger(char a)
{
	if(a>='0' && a<='9')
		return true;
	return false;
}
bool IsLetter(char a)
{
	if(a>='a' && a<='z')
		return true;
	if(a>='A' && a<='Z')
		return true;
	return false;
}
int Is_constant(char a[])
{
	int len=strlen(a);
	int flag=1;
	int w=1;
	for(int j=0;j<len;++j)
	{
		if(IsInteger(a[j])&&(flag==1||flag==2||flag==3||flag==4||flag==5))
		{
		    if(a[j]==0&&j==0){flag=8;w=3;}
		    if(flag==1){
                w=3;
		    }
		    if(flag==2){
                w=w>4?w:4;
                flag=5;//ΪС��
		    }
		    if(flag==3){
                w=5;
                flag=1;
		    }
		    if(flag==4){
                w=5;
                flag=1;
		    }

		}else if(a[j]=='.'&&(flag==1||flag==8)){
		    if(j==len-1||j==0){
                cout<<"�Ƿ�����"<<endl;
                return 0;
		    }
			w=w>4?w:4;
			flag=2;
		}else if(a[j]=='e'&&(flag==1||flag==5)){
			if(j==len-1||j==0) return 0;
			w=5;
			flag=3;
		}else if((a[j]=='+'||a[j]=='-')&&(flag==1||flag==3||flag==5)){
			if(j==len-1) return 0;
			if(a[j]=='+'&&j==0)return 0;
			w=5;
			flag=4;
		}else if(a[j]=='i'&&(flag==1||flag==5)){
			if(j!=len-1) return 0;
			w=5;
			flag=1;
		}else if(a[j]=='f'&&flag==5){
			if(j!=len-1) return 0;
			if(j==len-1&&w!=4) return 0;
		}else{
		    return 0;
		}

	}
	if(w==4&&a[len-1]!='f') w=5;
	if(flag==1||flag==5||flag==8) return w;
	else return 0;
}
bool Is_ID(char a[])
{
	int len=strlen(a);
	for(int j=0;j<len;++j)
	{
		if(IsLetter(a[j])||IsInteger(a[j])||a[j]=='_')
		{
			continue;
		}else{
			cout<<"�Ƿ�����"<<endl;
			return false;
		}
	}
	return true;
}
bool IsKeyword(char a[])
{
	int len=strlen(a);
	for(int j=0;j<num_of_keyword;++j)
	{
		if(strlen(keyword[j])==len)
		{
			if(strcmp(keyword[j],a)==0)
				return true;
		}
	}
	return false;
}
bool IsMO(char a)
{
	for(int i=0;i<num_of_MO;++i)
	{
		if(Monocular_Operator[i]==a)
			return true;
	}
	return false;
}
bool IsBO(char a[])
{
	for(int i=0;i<num_of_BO;++i)
	{
		if(strcmp(Binocular_Operator[i],a)==0)
			return true;
	}
	return false;
}
bool IsDelimiter(char a)
{
	for(int i=0;i<num_of_D;++i)
	{
		if(Delimiter[i]==a)
			return true;
	}
	return false;
}

void scan()
{
	char str[100];
	char ch;
	int i,j;
	int point;
	int flag;
	int ans=0;
	ch=fgetc(file_source);
	bool finish=false;
	while(!finish)
	{
	 	flag=-1;
		point=0;
		if(IsInteger(ch)||(ch=='-'&&ans==5))     //��һ��ch
		{
			flag=1;
			str[point++]=ch;
			ch=fgetc(file_source);
			while(IsInteger(ch) || ch=='.' || ch=='+' || ch=='-'||ch=='e'||ch=='f'||ch=='i')
			{
				flag=1;
				str[point++]=ch;
				ch=fgetc(file_source);
			}
			str[point]='\0';


		}else if(ch==39){
            ch=fgetc(file_source);
            ans=3;
			output<<3;
            constant<<ch<<'\n';
            cout<<ch<<" "<<"����"<<endl;
            constant<<2<<'\n';//����char�ͳ���
            ch=fgetc(file_source);
            if(ch!=39){
                cout<<"ȱ�١� ";
                return;
            }
            ch=fgetc(file_source);
		}else if(ch==34){
            ch=fgetc(file_source);
            while(ch!=34){
                if(ch=='\n' || ch=='\t'||ch==';'){
                    cout<<"ȱ��˫����";
                    return;
                }
                str[point++]=ch;
                ch=fgetc(file_source);
            }
            if(point==0){
                constant<<""<<'\n';
                ans=3;
				output<<3;
                cout<<" "<<"����"<<endl;
                constant<<6<<'\n';////����string�ͳ���
            }
            str[point]='\0';
            cout<<str<<" "<<"����"<<endl;
            ans=3;
			output<<3;
            constant<<str<<'\n';
            constant<<6<<'\n';
            point=0;
			flag=-1;
			ch=fgetc(file_source);
		}else if(IsLetter(ch)||ch=='_')
		{
			flag=2;
			str[point++]=ch;
			ch=fgetc(file_source);
			while(IsLetter(ch) || IsInteger(ch)||ch=='_')
			{
				flag=2;
				str[point++]=ch;
				ch=fgetc(file_source);
			}
			str[point]='\0';
		}else if(IsDelimiter(ch))
		{
			if(IsMO(ch)){
				if(ans==2||ans==3){
                    str[point++]=ch;
			if((ch=fgetc(file_source))==EOF)
			{
				finish=true;
			}
			str[point++]=ch;
			str[point]='\0';
			if(finish==false && IsBO(str))
			{
				cout<<str<<" "<<"˫Ŀ�����"<<endl;
				output<<str;
				ch=fgetc(file_source);
			}
			else
			{
				cout<<str[0]<<" "<<"��Ŀ�����"<<endl;
				if(str[0]=='=')ans=5;
				output<<str[0];
			}
			point=0;
				}else{
					cout<<ch<<" "<<"���"<<endl;
					if(ch=='#')
						output<<'*';
					else
						output<<ch;
					if((ch=fgetc(file_source))==EOF)
					{
						finish=true;
						break;
					}
				}
			}else{
				cout<<ch<<" "<<"���"<<endl;
				if(ch=='#')
					output<<'*';
				else
					output<<ch;
				if((ch=fgetc(file_source))==EOF)
				{
					finish=true;
					break;
				}

			}
		}else if(IsMO(ch))
		{
			str[point++]=ch;
			if((ch=fgetc(file_source))==EOF)
			{
				finish=true;
			}
			str[point++]=ch;
			str[point]='\0';
			if(finish==false && IsBO(str))
			{
				cout<<str<<" "<<"˫Ŀ�����"<<endl;
				output<<str;
				ch=fgetc(file_source);
			}
			else
			{
				cout<<str[0]<<" "<<"��Ŀ�����"<<endl;
				if(str[0]=='=')ans=5;
				output<<str[0];
			}
			point=0;
		}else if(ch==' ' || ch=='\n' || ch=='\t')
		{
			if((ch=fgetc(file_source))==EOF)
			{
				finish=true;
				break;
			}
			continue;
		}else{
			cout<<ch<<" "<<"�Ƿ��ַ�"<<endl;
			ch=fgetc(file_source);
		}
        if(flag==2)
		{
			if(IsKeyword(str))
			{
				cout<<str<<" "<<"�ؼ���"<<endl;
				ans=1;
				output<<f(str);
			}
			else
			{
			    //cout<<str<<endl;
			    string a="true";
			    string b="false";
				if(str==a||str==b||Is_ID(str))
				{
				    if(str==a){
                        cout<<str<<" "<<"����"<<endl;
                        ans=3;
                        output<<3;
                        constant<<str<<'\n';
                        constant<<1<<'\n';
				    }else if(str==b){
                        cout<<str<<" "<<"����"<<endl;
                        ans=3;
                        output<<3;
                        constant<<str<<'\n';
                        constant<<1<<'\n';
				    }else{
					cout<<str<<" "<<"��ʶ��"<<endl;
					ans=2;
					output<<2;
					variation<<str<<'\n';
					}
				}
				else
				{
					cout<<str<<" "<<"�������Ǳ�ʶ��"<<endl;
				}
			}
			point=0;
			flag=-1;
		}else if(flag==1){
		    if(Is_constant(str))
			{
				cout<<str<<" "<<"����"<<endl;
				ans=3;
				output<<3;
				constant<<str<<'\n';
				constant<<Is_constant(str)<<'\n';
			}
			else
			{
				cout<<str<<" "<<"�������ǳ���"<<endl;
			}
			point=0;
			flag=-1;
		}
	}
	output<<'#';
}
void init()
{
	len_final=0;
	len_state=0;
	for(int i=0;i<100;++i)
	{
		//is_final[i]=false;
		for(int j=0;j<100;++j)
			for(int k=0;k<100;++k)
				movel[i][j].set[k]='#';
	}
}
int main()
{
	init();
	file_source=fopen("�ʷ�����_Դ����.txt","r+");
	output.open("output.txt");
	constant.open("constant.txt");
	variation.open("variation.txt");
	scan();
	fclose(file_source);
	constant.close();
	variation.close();
	output.close();
	return 0;
}

}
int main(){
    stu::main();

    sta::main();
    return 0;
}

