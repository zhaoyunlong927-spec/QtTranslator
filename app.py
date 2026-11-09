import json
import queue
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
import hashlib
import secrets
import urllib.parse
import os
from collections import Counter
import re
import threading
import urllib.request
import xml.etree.ElementTree as ET
import tkinter as tk
from tkinter import filedialog, messagebox, ttk

TOKEN = re.compile(r'%L?(?:[1-9][0-9]?|n)|<[^>]+>|&(?:[A-Za-z][A-Za-z0-9]+|#(?:[0-9]+|x[0-9A-Fa-f]+));|\\(?:\\|[nrt])|\n')


class PlaceholderError(ValueError):
    pass


def translate(text, provider, url, key, model, source, target, appid="", allow_fallback=True):
    saved = []
    nonce = secrets.token_hex(8).upper()
    marker_prefix = f'__QT_{nonce}_'
    def protect(match):
        saved.append(match.group())
        return f'{marker_prefix}{len(saved)-1}__'
    protected = TOKEN.sub(protect, text)
    if provider == '百度翻译':
        if not appid or not key:
            raise ValueError('百度翻译需要 APP ID 和密钥')
        salt = str(secrets.randbits(64))
        sign = hashlib.md5((appid + protected + salt + key).encode('utf-8')).hexdigest()
        def baidu_language(value):
            value = value.strip().lower().replace('_', '-')
            mapping = {'zh-cn': 'zh', 'zh-hans': 'zh', 'zh-tw': 'cht', 'zh-hant': 'cht', 'en-us': 'en', 'en-gb': 'en', 'ja': 'jp', 'ko': 'kor', 'fr': 'fra', 'es': 'spa', 'ar': 'ara', 'pt': 'pt', 'ru': 'ru', 'de': 'de', 'it': 'it'}
            return mapping.get(value, value)
        payload = {'q': protected, 'from': baidu_language(source) or 'auto', 'to': baidu_language(target), 'appid': appid, 'salt': salt, 'sign': sign}
        request = urllib.request.Request(url, data=urllib.parse.urlencode(payload).encode('utf-8'), headers={'Content-Type': 'application/x-www-form-urlencoded'})
        with urllib.request.urlopen(request, timeout=120) as response:
            result = json.load(response)
        if 'error_code' in result:
            raise ValueError(f"百度翻译错误 {result['error_code']}: {result.get('error_msg', '')}")
        output = '\n'.join(item['dst'] for item in result['trans_result'])
    elif provider == 'LibreTranslate':
        payload = {'q': protected, 'source': source or 'auto', 'target': target, 'format': 'text', 'api_key': key}
    else:
        payload = {'model': model, 'messages': [{'role': 'system', 'content': f'Translate the user text from {source or "auto-detected language"} to {target}. Return only the translation. Preserve every placeholder marker beginning with __QT_ exactly, including all characters and underscores.'}, {'role': 'user', 'content': protected}], 'stream': False}
    if provider != '百度翻译':
        headers = {'Content-Type': 'application/json'}
        if key and provider != 'LibreTranslate':
            headers['Authorization'] = 'Bearer ' + key
        request = urllib.request.Request(url, data=json.dumps(payload).encode('utf-8'), headers=headers)
        with urllib.request.urlopen(request, timeout=120) as response:
            result = json.load(response)
        if provider == 'LibreTranslate':
            output = result['translatedText']
        elif provider == 'Ollama':
            output = result['message']['content']
        else:
            output = result['choices'][0]['message']['content']
    if not isinstance(output, str) or (text.strip() and not output.strip()):
        raise ValueError('翻译服务返回空译文')
    expected_markers = [f'{marker_prefix}{i}__' for i in range(len(saved))]
    found_markers = re.findall(re.escape(marker_prefix) + r'\d+__', output)
    markers_ok = Counter(found_markers) == Counter(expected_markers) and output.count(marker_prefix) == len(saved)
    if not markers_ok:
        if not allow_fallback:
            raise PlaceholderError('翻译服务未正确保留占位符')
        # Retry text fragments independently, leaving every original token untouched.
        fragments = TOKEN.split(text)
        translated = []
        for index, fragment in enumerate(fragments):
            if fragment.strip():
                leading = fragment[:len(fragment) - len(fragment.lstrip())]
                trailing = fragment[len(fragment.rstrip()):]
                core = fragment.strip()
                translated.append(leading + translate(core, provider, url, key, model, source, target, appid, False) + trailing)
            else:
                translated.append(fragment)
            if index < len(saved):
                translated.append(saved[index])
        output = ''.join(translated)
        if Counter(TOKEN.findall(text)) != Counter(TOKEN.findall(output)):
            raise PlaceholderError('分段翻译后占位符仍不匹配')
        return output
    for i, token in enumerate(saved):
        output = output.replace(expected_markers[i], token)
    if Counter(TOKEN.findall(text)) != Counter(TOKEN.findall(output)):
        raise PlaceholderError('翻译结果中的占位符或转义标记不匹配')
    return output



def entry_status(source, tr, plural=False):
    kind = tr.get('type', '')
    if kind in ('obsolete', 'vanished'):
        return '已过时'
    if plural:
        return '复数条目'
    text = tr.text or ''
    if not text.strip():
        return '未翻译'
    if kind == 'unfinished':
        return '待确认'
    if Counter(TOKEN.findall(source)) != Counter(TOKEN.findall(text)):
        return '占位符异常'
    return '已完成'


class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title('Qt Translator · 翻译工作台')
        self.geometry('1180x760')
        self.minsize(850, 600)
        self.configure(bg='#f3f5fa')
        self.tree = None
        self.path = None
        self.items = []
        self.busy = False
        self.failures = {}
        self.selected_context = None
        self.context_ids = {}
        self.events = queue.Queue()
        self.pause_event = threading.Event()
        self.stop_event = threading.Event()
        self.provider = tk.StringVar(value='OpenAI 兼容 API')
        self.url = tk.StringVar(value='https://api.openai.com/v1/chat/completions')
        self.key = tk.StringVar()
        self.model = tk.StringVar(value='gpt-4o-mini')
        self.appid = tk.StringVar()
        self.config_path = os.path.join(os.getcwd(), 'qt_translator_config.json')
        self.provider_configs = {}
        self.current_provider = self.provider.get()
        self.source = tk.StringVar()
        self.target = tk.StringVar(value='zh')
        self.overwrite = tk.BooleanVar()
        self.workers = tk.StringVar(value='1')
        self.search = tk.StringVar()
        self.filter = tk.StringVar(value='全部状态')
        self.status = tk.StringVar(value='打开一个 Qt TS 文件开始')
        self.summary = tk.StringVar(value='尚未加载文件')
        self.load_config()
        style = ttk.Style(self)
        style.theme_use('clam')
        style.configure('.', font=('Microsoft YaHei UI', 9), background='#f3f5fa', foreground='#26334d')
        style.configure('TButton', padding=(14, 7))
        style.configure('Accent.TButton', background='#4f63e9', foreground='white', borderwidth=0)
        style.map('Accent.TButton', background=[('active', '#4053d0'), ('disabled', '#aab2df')])
        style.configure('Treeview', rowheight=31, background='white', fieldbackground='white', borderwidth=0)
        style.configure('Treeview.Heading', font=('Microsoft YaHei UI', 9, 'bold'), background='#e8ecf5', relief='flat', padding=7)
        style.map('Treeview', background=[('selected', '#e0e6ff')], foreground=[('selected', '#202d59')])
        header = tk.Frame(self, bg='#202b55', padx=22, pady=15)
        header.pack(fill='x')
        tk.Label(header, text='Qt Translator', font=('Microsoft YaHei UI', 18, 'bold'), fg='white', bg='#202b55').pack(anchor='w')
        tk.Label(header, text='让 Qt 多语言翻译更清晰、更高效', fg='#c8d1f2', bg='#202b55', font=('Microsoft YaHei UI', 9)).pack(anchor='w')
        container = ttk.Frame(self, padding=16)
        container.pack(fill='both', expand=True)
        toolbar = ttk.Frame(container)
        toolbar.pack(fill='x', pady=(0, 10))
        self.open_button = ttk.Button(toolbar, text='打开 TS 文件', command=self.open_file)
        self.open_button.pack(side='left')
        self.run_button = ttk.Button(toolbar, text='开始智能翻译', style='Accent.TButton', command=self.start)
        self.run_button.pack(side='left', padx=8)
        self.save_button = ttk.Button(toolbar, text='另存为', command=self.save)
        self.save_button.pack(side='left')
        self.pause_button = ttk.Button(toolbar, text='暂停', command=self.toggle_pause, state='disabled')
        self.pause_button.pack(side='left', padx=(12, 5))
        self.stop_button = ttk.Button(toolbar, text='停止', command=self.stop, state='disabled')
        self.stop_button.pack(side='left')
        ttk.Label(toolbar, textvariable=self.summary).pack(side='right')
        settings = ttk.LabelFrame(container, text=' 翻译设置 ', padding=10)
        settings.pack(fill='x')
        self.setting_fields = {}
        fields = [('服务', self.provider), ('接口地址', self.url), ('API 密钥', self.key), ('模型', self.model), ('源语言', self.source), ('目标语言', self.target), ('百度 APP ID', self.appid)]
        for i, (label, var) in enumerate(fields):
            row, col = divmod(i, 3)
            box = ttk.Frame(settings)
            self.setting_fields[label] = box
            ttk.Label(box, text=label).pack(anchor='w')
            if i == 0:
                widget = ttk.Combobox(box, textvariable=var, values=['OpenAI 兼容 API', 'LibreTranslate', 'Ollama', '百度翻译'], state='readonly')
                widget.bind('<<ComboboxSelected>>', self.provider_changed)
            elif i == 3:
                widget = ttk.Combobox(box, textvariable=var, values=['gpt-4o-mini', 'gpt-4.1-mini', 'qwen2.5', 'qwen3', 'llama3.2'])
            elif i in (4, 5):
                widget = ttk.Combobox(box, textvariable=var, values=['', 'auto', 'zh-CN', 'zh-TW', 'en', 'en-US', 'ja', 'ko', 'fr', 'de', 'es', 'ru', 'it', 'pt'])
            else:
                widget = ttk.Entry(box, textvariable=var, show='•' if i == 2 else '')
            widget.pack(fill='x', pady=(3, 0))
            settings.columnconfigure(col, weight=1)
        self.update_setting_fields()
        ttk.Checkbutton(settings, text='重新翻译已完成条目', variable=self.overwrite).grid(row=3, column=0, sticky='w', padx=5, pady=(6, 0))
        worker_box = ttk.Frame(settings)
        worker_box.grid(row=3, column=1, sticky='w', padx=5)
        ttk.Label(worker_box, text='并发数').pack(side='left')
        ttk.Combobox(worker_box, textvariable=self.workers, values=['1', '2', '3', '4', '5', '8'], state='readonly', width=4).pack(side='left', padx=6)
        ttk.Button(settings, text='保存配置', command=self.save_config).grid(row=3, column=2, sticky='e', padx=5, pady=(6, 0))
        self.protocol('WM_DELETE_WINDOW', self.close_window)
        tools = ttk.Frame(container)
        tools.pack(fill='x', pady=(14, 8))
        ttk.Label(tools, text='翻译条目', font=('Microsoft YaHei UI', 11, 'bold')).pack(side='left')
        for label, action in [('← 上一条', lambda: self.navigate(-1)), ('下一条 →', lambda: self.navigate(1)), ('← 上一待处理', lambda: self.navigate(-1, True)), ('下一待处理 →', lambda: self.navigate(1, True)), ('✓ 确认', lambda: self.confirm_translation(False)), ('✓ 确认并下一条', lambda: self.confirm_translation(True))]:
            ttk.Button(tools, text=label, command=action, padding=(6, 3)).pack(side='left', padx=(6, 0))
        self.search_entry = ttk.Entry(tools, textvariable=self.search, width=22)
        self.search_entry.pack(side='right', padx=(8, 0))
        self.bind('<Control-f>', self.focus_search)
        self.bind('<Control-F>', self.focus_search)
        self.bind('<Escape>', self.clear_search)
        ttk.Label(tools, text='搜索').pack(side='right')
        box = ttk.Combobox(tools, textvariable=self.filter, values=['全部状态', '未翻译', '待确认', '已完成', '占位符异常', '翻译失败', '复数条目', '已过时'], width=13, state='readonly')
        box.pack(side='right', padx=8)
        self.search.trace_add('write', lambda *_: self.refresh())
        self.filter.trace_add('write', lambda *_: self.refresh())
        panes = ttk.Panedwindow(container, orient='horizontal')
        panes.pack(fill='both', expand=True)
        groups = ttk.LabelFrame(panes, text=' 上下文分组 ')
        panes.add(groups, weight=1)
        group_scroll = ttk.Scrollbar(groups, orient='vertical')
        group_scroll.pack(side='right', fill='y')
        self.context_list = ttk.Treeview(groups, columns=('progress',), show='tree headings', selectmode='browse', yscrollcommand=group_scroll.set)
        self.context_list.heading('#0', text='上下文', anchor='w')
        self.context_list.heading('progress', text='完成', anchor='center')
        self.context_list.column('#0', width=180, minwidth=100)
        self.context_list.column('progress', width=65, minwidth=55, stretch=False, anchor='center')
        self.context_list.pack(fill='both', expand=True)
        group_scroll.config(command=self.context_list.yview)
        self.context_list.bind('<<TreeviewSelect>>', self.select_context)
        table = ttk.Frame(panes)
        panes.add(table, weight=4)
        self.list = ttk.Treeview(table, columns=('state', 'context', 'source', 'translation'), show='headings', selectmode='browse')
        for name, title, width in [('state', '状态', 90), ('context', '上下文', 150), ('source', '原文', 360), ('translation', '译文', 360)]:
            self.list.heading(name, text=title, anchor='w')
            self.list.column(name, width=width, minwidth=65, stretch=name != 'state')
        scroll = ttk.Scrollbar(table, orient='vertical', command=self.list.yview)
        self.list.configure(yscrollcommand=scroll.set)
        scroll.pack(side='right', fill='y')
        self.list.pack(side='left', fill='both', expand=True)
        for tag, color in [('未翻译', '#fff7e9'), ('待确认', '#fff7e9'), ('占位符异常', '#fff0ef'), ('翻译失败', '#fff0ef'), ('已过时', '#eef0f4'), ('已完成', '#f4fbf6')]:
            self.list.tag_configure(tag, background=color)
        self.list.bind('<Double-1>', self.edit)
        self.list.bind('<<TreeviewSelect>>', self.show_details)
        self.details = tk.StringVar(value='选择条目查看占位符；双击可编辑译文')
        ttk.Label(container, textvariable=self.details, wraplength=1050).pack(anchor='w', pady=(10, 3))
        ttk.Label(container, textvariable=self.status, foreground='#68758d').pack(anchor='w')

    def capture_provider(self):
        self.provider_configs[self.current_provider] = {
            'url': self.url.get(), 'key': self.key.get(),
            'model': self.model.get(), 'appid': self.appid.get(),
        }

    def load_config(self):
        try:
            with open(self.config_path, encoding='utf-8') as stream:
                config = json.load(stream)
            self.provider_configs = config.get('providers', {})
            selected = config.get('provider', self.provider.get())
            if selected not in ('OpenAI 兼容 API', 'LibreTranslate', 'Ollama', '百度翻译'):
                selected = 'OpenAI 兼容 API'
            self.provider.set(selected)
            self.current_provider = selected
            self.source.set(config.get('source', ''))
            self.target.set(config.get('target', 'zh'))
            self.overwrite.set(config.get('overwrite', False))
            workers = str(config.get('workers', '1'))
            self.workers.set(workers if workers in ('1', '2', '3', '4', '5', '8') else '1')
            self.restore_provider(selected)
        except FileNotFoundError:
            pass
        except (OSError, ValueError, TypeError, AttributeError) as e:
            messagebox.showwarning('读取配置失败', f'无法读取配置，将使用默认值：{e}')

    def restore_provider(self, provider):
        defaults = {'OpenAI 兼容 API': ('https://api.openai.com/v1/chat/completions', 'gpt-4o-mini'), 'LibreTranslate': ('http://localhost:5000/translate', ''), 'Ollama': ('http://localhost:11434/api/chat', 'qwen2.5'), '百度翻译': ('https://fanyi-api.baidu.com/api/trans/vip/translate', '')}
        saved = self.provider_configs.get(provider, {})
        url, model = defaults[provider]
        self.url.set(saved.get('url', url))
        self.key.set(saved.get('key', ''))
        self.model.set(saved.get('model', model))
        self.appid.set(saved.get('appid', ''))

    def provider_changed(self, event=None):
        self.capture_provider()
        self.current_provider = self.provider.get()
        self.restore_provider(self.current_provider)
        self.update_setting_fields()

    def update_setting_fields(self):
        common = ['服务', '接口地址']
        specific = {
            'OpenAI 兼容 API': ['API 密钥', '模型'],
            'LibreTranslate': ['API 密钥'],
            'Ollama': ['API 密钥', '模型'],
            '百度翻译': ['百度 APP ID', 'API 密钥'],
        }
        visible = common + specific[self.provider.get()] + ['源语言', '目标语言']
        for field in self.setting_fields.values():
            field.grid_remove()
        for i, name in enumerate(visible):
            row, col = divmod(i, 3)
            self.setting_fields[name].grid(row=row, column=col, sticky='ew', padx=5, pady=3)

    def save_config(self):
        self.capture_provider()
        config = {'provider': self.provider.get(), 'providers': self.provider_configs,
                  'source': self.source.get(), 'target': self.target.get(), 'overwrite': self.overwrite.get(), 'workers': self.workers.get()}
        try:
            with open(self.config_path, 'w', encoding='utf-8') as stream:
                json.dump(config, stream, ensure_ascii=False, indent=2)
            self.status.set(f'配置已保存：{self.config_path}（密钥以明文保存）')
            return True
        except OSError as e:
            messagebox.showerror('保存配置失败', str(e))
            return False

    def close_window(self):
        if self.busy:
            messagebox.showwarning('翻译进行中', '请等待当前翻译结束后再关闭。')
            return
        if self.save_config():
            self.destroy()

    def open_file(self):
        path = filedialog.askopenfilename(filetypes=[('Qt TS', '*.ts')])
        if not path: return
        try:
            parser = ET.XMLParser(target=ET.TreeBuilder(insert_comments=True))
            tree = ET.parse(path, parser=parser)
            if tree.getroot().tag != 'TS': raise ValueError('不是 Qt TS 文件')
            items = []
            for context in tree.findall('context'):
                name = context.findtext('name', default='')
                for msg in context.findall('message'):
                    source = msg.findtext('source', default='')
                    tr = msg.find('translation')
                    if tr is None:
                        tr = ET.SubElement(msg, 'translation', {'type': 'unfinished'})
                    if source: items.append((source, tr, name, msg.get('numerus') == 'yes'))
            self.tree, self.path, self.items = tree, path, items
            self.selected_context = None
            self.failures.clear()
            language = tree.getroot().get('language', '')
            if language: self.target.set(language.replace('_', '-'))
            self.refresh()
            self.status.set(f'已打开 {os.path.basename(path)}。双击条目编辑；复数及过时条目不会自动翻译。')
        except Exception as e: messagebox.showerror('打开失败', str(e))

    def refresh(self):
        selected = self.list.selection()
        position = self.list.yview()[0]
        group_position = self.context_list.yview()[0]
        self.list.delete(*self.list.get_children())
        self.context_list.delete(*self.context_list.get_children())
        counts = Counter()
        groups = {}
        query = self.search.get().casefold().strip()
        symbols = {'已完成': '✓', '未翻译': '○', '待确认': '?', '占位符异常': '!', '翻译失败': '!', '复数条目': '≡', '已过时': '–'}
        for i, (source, tr, context, plural) in enumerate(self.items):
            state = '翻译失败' if i in self.failures else entry_status(source, tr, plural)
            counts[state] += 1
            if context not in groups: groups[context] = [0, 0, 0]
            if state != '已过时':
                groups[context][1] += 1
                if state == '已完成': groups[context][0] += 1
                if state in ('占位符异常', '翻译失败'): groups[context][2] += 1
            translation = ' / '.join((x.text or '') for x in tr.findall('numerusform')) if plural else (tr.text or '')
            if self.selected_context is not None and context != self.selected_context: continue
            if self.filter.get() != '全部状态' and state != self.filter.get(): continue
            if query and query not in (source + ' ' + translation + ' ' + context).casefold(): continue
            self.list.insert('', 'end', iid=str(i), values=(f'{symbols[state]} {state}', context, source, translation), tags=(state,))
        self.context_ids = {'all': None}
        self.context_list.insert('', 'end', iid='all', text='全部上下文', values=(f'{counts["已完成"]}/{sum(g[1] for g in groups.values())}',))
        for number, (context, (finished, total, errors)) in enumerate(groups.items()):
            group_id = f'g{number}'
            self.context_ids[group_id] = context
            symbol = '–' if not total else ('!' if errors else ('✓' if finished == total else '○'))
            self.context_list.insert('', 'end', iid=group_id, text=f'{symbol} {context or "（无上下文）"}', values=(f'{finished}/{total}',))
        selected_group = next((key for key, value in self.context_ids.items() if value == self.selected_context), 'all')
        self.context_list.selection_set(selected_group)
        self.context_list.yview_moveto(group_position)
        self.list.yview_moveto(position)
        if selected and self.list.exists(selected[0]):
            self.list.selection_set(selected[0])
        self.summary.set(f'共 {len(self.items)} 条  ·  已完成 {counts["已完成"]}  ·  待处理 {counts["未翻译"] + counts["待确认"]}  ·  异常 {counts["占位符异常"] + counts["翻译失败"]}')

    def select_context(self, event=None):
        selection = self.context_list.selection()
        if not selection: return
        context = self.context_ids.get(selection[0])
        if context != self.selected_context:
            self.selected_context = context
            self.refresh()

    def focus_search(self, event=None):
        self.search_entry.focus_set()
        self.search_entry.selection_range(0, 'end')
        return 'break'

    def clear_search(self, event=None):
        if self.focus_get() == self.search_entry:
            self.search.set('')
            return 'break'

    def navigate(self, direction, unfinished=False):
        rows = list(self.list.get_children())
        if not rows: return
        selected = self.list.selection()
        current = rows.index(selected[0]) if selected and selected[0] in rows else (-1 if direction > 0 else len(rows))
        for pos in range(current + direction, len(rows) if direction > 0 else -1, direction):
            row = rows[pos]
            i = int(row)
            state = '翻译失败' if i in self.failures else entry_status(self.items[i][0], self.items[i][1], self.items[i][3])
            if unfinished and state not in ('未翻译', '待确认', '占位符异常', '翻译失败'): continue
            self.list.selection_set(row)
            self.list.focus(row)
            self.list.see(row)
            self.show_details()
            return
        self.status.set('当前分组和筛选范围内没有更多符合条件的条目。')

    def confirm_translation(self, advance=False):
        if self.busy:
            self.status.set('请在批量翻译结束后确认译文。')
            return
        selected = self.list.selection()
        if not selected: return
        index = int(selected[0])
        source, tr, context, plural = self.items[index]
        value = tr.text or ''
        if plural or tr.get('type') in ('obsolete', 'vanished'):
            return messagebox.showinfo('提示', '复数和过时条目请在 Qt Linguist 中处理。')
        if not value.strip(): return messagebox.showwarning('无法确认', '译文为空，请先填写译文。')
        if Counter(TOKEN.findall(source)) != Counter(TOKEN.findall(value)):
            return messagebox.showwarning('无法确认', '原文和译文的标记不匹配，请先修正。')
        visible_rows = list(self.list.get_children())
        next_rows = visible_rows[visible_rows.index(selected[0]) + 1:] if advance else []
        tr.attrib.pop('type', None)
        self.failures.pop(index, None)
        self.refresh()
        self.status.set('译文已确认；请使用“另存为”保存 TS 文件。')
        if advance:
            for row in next_rows:
                if self.list.exists(row):
                    self.list.selection_set(row)
                    self.list.focus(row)
                    self.list.see(row)
                    self.show_details()
                    break

    def show_details(self, event=None):
        selected = self.list.selection()
        if not selected: return
        index = int(selected[0])
        source, tr, context, plural = self.items[index]
        original = TOKEN.findall(source)
        result = TOKEN.findall(tr.text or '') if not plural else []
        self.details.set(f'上下文：{context}    原文标记：{original or "无"}    译文标记：{result or "无"}' + ('    复数条目请使用 Qt Linguist 编辑' if plural else '') + (f'    翻译失败：{self.failures[index]}' if index in self.failures else ''))

    def edit(self, event):
        if self.busy: return
        selected = self.list.selection()
        if not selected: return
        index = int(selected[0])
        source, tr, context, plural = self.items[index]
        if plural or tr.get('type') in ('obsolete', 'vanished'):
            return messagebox.showinfo('提示', '复数和过时条目请在 Qt Linguist 中编辑。')
        dialog = tk.Toplevel(self)
        dialog.title('编辑译文')
        dialog.geometry('720x510')
        dialog.minsize(520, 400)
        dialog.transient(self)
        dialog.grab_set()
        frame = ttk.Frame(dialog, padding=16)
        frame.pack(fill='both', expand=True)
        ttk.Label(frame, text=f'上下文：{context}', font=('Microsoft YaHei UI', 10, 'bold')).pack(anchor='w')
        ttk.Label(frame, text='原文').pack(anchor='w', pady=(10, 3))
        original = tk.Text(frame, height=4, wrap='word', font=('Microsoft YaHei UI', 10))
        original.pack(fill='x')
        original.insert('1.0', source)
        original.config(state='disabled')
        ttk.Label(frame, text='译文（可直接编辑）').pack(anchor='w', pady=(10, 3))
        editor = tk.Text(frame, height=6, wrap='word', font=('Microsoft YaHei UI', 10), undo=True)
        editor.pack(fill='both', expand=True)
        editor.insert('1.0', tr.text or '')
        info = tk.StringVar(value='可自动翻译、编辑并检查标记；保存后还需在主窗口另存 TS 文件。')
        ttk.Label(frame, textvariable=info, wraplength=680).pack(anchor='w', pady=8)
        controls = ttk.Frame(frame)
        controls.pack(fill='x')
        result_queue = queue.Queue()
        working = False

        def get_value():
            return editor.get('1.0', 'end-1c')

        def check():
            missing = Counter(TOKEN.findall(source)) - Counter(TOKEN.findall(get_value()))
            extra = Counter(TOKEN.findall(get_value())) - Counter(TOKEN.findall(source))
            if missing or extra:
                info.set(f'标记不匹配：缺少 {list(missing.elements()) or "无"}；多出 {list(extra.elements()) or "无"}')
                return False
            info.set('占位符、标签和转义标记检查通过。')
            return True

        def insert_missing():
            missing = Counter(TOKEN.findall(source)) - Counter(TOKEN.findall(get_value()))
            if not missing:
                info.set('没有缺少的标记。')
                return
            editor.insert('insert', ''.join(missing.elements()))
            editor.focus_set()
            check()

        def poll():
            nonlocal working
            if not dialog.winfo_exists(): return
            try:
                ok, value = result_queue.get_nowait()
            except queue.Empty:
                dialog.after(50, poll)
                return
            working = False
            editor.config(state='normal')
            translate_button.config(state='normal')
            if ok:
                editor.delete('1.0', 'end')
                editor.insert('1.0', value)
                check()
            else:
                info.set(f'翻译失败：{value}')

        def translate_one():
            nonlocal working
            if working: return
            if not self.target.get().strip():
                info.set('请先在主窗口填写目标语言。')
                return
            if get_value().strip() and not messagebox.askyesno('替换译文', '自动翻译会替换当前编辑框中的译文，是否继续？', parent=dialog):
                return
            settings = (self.provider.get(), self.url.get(), self.key.get(), self.model.get(), self.source.get(), self.target.get(), self.appid.get())
            working = True
            editor.config(state='disabled')
            translate_button.config(state='disabled')
            info.set('正在翻译，请稍候…')
            def worker():
                try: result_queue.put((True, translate(source, *settings)))
                except Exception as error: result_queue.put((False, str(error)))
            threading.Thread(target=worker, daemon=True).start()
            dialog.after(50, poll)

        def save_edit():
            if working: return
            value = get_value()
            if value and not check() and not messagebox.askyesno('标记不匹配', '原文和译文的标记不一致。仍要保存为待确认吗？', parent=dialog):
                return
            tr.text = value
            self.failures.pop(index, None)
            if value and Counter(TOKEN.findall(source)) == Counter(TOKEN.findall(value)):
                tr.attrib.pop('type', None)
            else:
                tr.set('type', 'unfinished')
            dialog.destroy()
            self.refresh()

        translate_button = ttk.Button(controls, text='自动翻译', command=translate_one)
        translate_button.pack(side='left')
        ttk.Button(controls, text='检查标记', command=check).pack(side='left', padx=5)
        ttk.Button(controls, text='插入缺失标记', command=insert_missing).pack(side='left')
        ttk.Button(controls, text='取消', command=dialog.destroy).pack(side='right')
        ttk.Button(controls, text='保存译文', style='Accent.TButton', command=save_edit).pack(side='right', padx=5)
        editor.focus_set()

    def start(self):
        if self.tree is None: return messagebox.showwarning('提示', '请先打开 TS 文件')
        if not self.target.get().strip(): return messagebox.showwarning('提示', '请填写目标语言')
        settings = (self.provider.get(), self.url.get(), self.key.get(), self.model.get(), self.source.get(), self.target.get(), self.appid.get())
        pending = [(i, source) for i, (source, tr, context, plural) in enumerate(self.items) if not plural and tr.get('type') not in ('obsolete', 'vanished') and (self.overwrite.get() or entry_status(source, tr) in ('未翻译', '待确认'))]
        if not pending:
            self.status.set('没有需要翻译的条目。')
            return
        try:
            workers = int(self.workers.get())
            if workers not in (1, 2, 3, 4, 5, 8): raise ValueError()
        except ValueError:
            return messagebox.showwarning('提示', '请选择有效的并发数')
        self.failures.clear()
        self.refresh()
        self.busy = True
        self.pause_event.clear()
        self.stop_event.clear()
        for button in (self.run_button, self.open_button, self.save_button): button.config(state='disabled')
        self.pause_button.config(state='normal', text='暂停')
        self.stop_button.config(state='normal')
        self.status.set(f'开始翻译，共 {len(pending)} 条，并发数 {workers}')

        def worker():
            waiting = iter(pending)
            active = {}
            completed = 0
            failed = 0
            exhausted = False
            with ThreadPoolExecutor(max_workers=workers) as pool:
                while True:
                    while not exhausted and not self.pause_event.is_set() and not self.stop_event.is_set() and len(active) < workers:
                        try:
                            i, source = next(waiting)
                        except StopIteration:
                            exhausted = True
                            break
                        active[pool.submit(translate, source, *settings)] = i
                    if not active:
                        if exhausted or self.stop_event.is_set(): break
                        self.stop_event.wait(0.1)
                        continue
                    done, _ = wait(active, timeout=0.1, return_when=FIRST_COMPLETED)
                    for future in done:
                        i = active.pop(future)
                        completed += 1
                        try:
                            result = future.result()
                        except Exception as error:
                            failed += 1
                            self.events.put(('error', i, str(error), completed, len(pending), failed))
                        else:
                            self.events.put(('result', i, result, completed, len(pending), failed))
            self.events.put(('finish', completed, len(pending), failed, self.stop_event.is_set()))

        threading.Thread(target=worker, daemon=True).start()
        self.after(50, self.process_events)

    def toggle_pause(self):
        if self.pause_event.is_set():
            self.pause_event.clear()
            self.pause_button.config(text='暂停')
            self.status.set('已继续翻译')
        else:
            self.pause_event.set()
            self.pause_button.config(text='继续')
            self.status.set('正在暂停：已发出的请求完成后将不再开始新请求')

    def stop(self):
        self.stop_event.set()
        self.pause_event.clear()
        self.pause_button.config(state='disabled')
        self.stop_button.config(state='disabled')
        self.status.set('正在停止，等待已发出的请求完成…')

    def process_events(self):
        while True:
            try:
                event = self.events.get_nowait()
            except queue.Empty:
                break
            kind = event[0]
            if kind == 'finish':
                _, completed, total, failed, stopped = event
                prefix = '已停止' if stopped else '翻译完成'
                self.finish(f'{prefix}：已处理 {completed}/{total} 条，失败 {failed} 条。选择失败条目可查看原因。')
                continue
            _, i, value, completed, total, failed = event
            if kind == 'result':
                self.apply(i, value)
            else:
                self.failures[i] = value
                self.refresh()
            if self.stop_event.is_set():
                state = '正在停止，等待已发出的请求完成'
            elif self.pause_event.is_set():
                state = '已暂停（进行中的请求仍会完成）'
            else:
                state = '正在翻译'
            self.status.set(f'{state}：{completed}/{total}，失败 {failed} 条')
        if self.busy:
            self.after(50, self.process_events)

    def apply(self, i, value):
        tr = self.items[i][1]
        tr.text = value
        tr.attrib.pop('type', None)
        self.failures.pop(i, None)
        self.refresh()

    def finish(self, text):
        self.busy = False
        for button in (self.run_button, self.open_button, self.save_button): button.config(state='normal')
        self.pause_button.config(state='disabled', text='暂停')
        self.stop_button.config(state='disabled')
        self.refresh()
        self.status.set(text)

    def save(self):
        if self.tree is None: return
        path = filedialog.asksaveasfilename(defaultextension='.ts', filetypes=[('Qt TS', '*.ts')], initialfile='translated.ts')
        if not path: return
        try:
            self.tree.write(path, encoding='utf-8', xml_declaration=True)
            self.status.set(f'已保存：{path}')
        except Exception as e: messagebox.showerror('保存失败', str(e))


if __name__ == '__main__':
    App().mainloop()
