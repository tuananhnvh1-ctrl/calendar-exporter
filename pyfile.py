# Required libraries: pip install icalendar python-dateutil
# -*- coding: utf-8 -*-

import csv
import os
import re
from datetime import datetime, timedelta
from zoneinfo import ZoneInfo, ZoneInfoNotFoundError

from dateutil.rrule import rrulestr
from icalendar import Calendar, vCalAddress

# --- Thêm thư viện cho giao diện đồ họa (có sẵn trong Python) ---
import tkinter as tk
from tkinter import filedialog, messagebox
import traceback

# ==============================================================================
# PHẦN LOGIC XỬ LÝ ICS -> CSV
# ==============================================================================

# --- Constants ---
try:
    VIETNAM_TZ = ZoneInfo("Asia/Ho_Chi_Minh")
except ZoneInfoNotFoundError:
    print("Error: Timezone 'Asia/Ho_Chi_Minh' not found.")
    exit(1)

def unfold_ics_content(file_path):
    with open(file_path, 'r', encoding='utf-8') as f:
        lines = f.readlines()
    unfolded_lines = []
    if not lines: return ""
    unfolded_lines.append(lines[0].strip())
    for i in range(1, len(lines)):
        line = lines[i]
        if line.startswith(' ') or line.startswith('\t'):
            unfolded_lines[-1] += line.strip()
        else:
            unfolded_lines.append(line.strip())
    return "\n".join(unfolded_lines)

def get_aware_datetime(dt_prop):
    if dt_prop is None:
        return None
    dt = dt_prop.dt
    if isinstance(dt, datetime):
        if dt.tzinfo is None:
            return dt.replace(tzinfo=VIETNAM_TZ)
        return dt
    return datetime(dt.year, dt.month, dt.day, tzinfo=VIETNAM_TZ)

def clean_description(desc):
    if not desc: return ""
    cleaned_desc = re.sub(r'-::~[\s\S]*::~-', '', str(desc)).strip()
    cleaned_desc = cleaned_desc.replace('\\n', ' ').replace('\n', ' ')
    return cleaned_desc

def extract_conference_link(event):
    if 'X-GOOGLE-CONFERENCE' in event:
        return event.get('X-GOOGLE-CONFERENCE')

    description = str(event.get('description', ''))
    location = str(event.get('location', ''))
    full_text = description + " " + location

    patterns = [
        r'https?://meet\.google\.com/[a-zA-Z0-9_-]+',
        r'https?://[a-zA-Z0-9-]+\.zoom\.us/j/[a-zA-Z0-9_.-]+',
        r'https?://teams\.microsoft\.com/l/meetup-join/[a-zA-Z0-9_.-]+'
    ]
    for pattern in patterns:
        match = re.search(pattern, full_text)
        if match:
            return match.group(0)
    return ""

def fix_rrule_until_timezone(rrule_str: str, dtstart_tz: ZoneInfo) -> str:
    malformed_match = re.search(r'(UNTIL=[0-9]{8}T[0-9]{6}Z)T[0-9]{6}Z', rrule_str)
    if malformed_match:
        correct_until = malformed_match.group(1)
        return re.sub(r'UNTIL=[0-9TZ]+', correct_until, rrule_str)

    non_utc_match = re.search(r'UNTIL=([0-9]{8}(T[0-9]{6})?)(?!Z)', rrule_str)
    if non_utc_match:
        until_local_str = non_utc_match.group(1)
        try:
            if 'T' in until_local_str:
                naive_until_dt = datetime.strptime(until_local_str, '%Y%m%dT%H%M%S')
            else:
                naive_until_dt = datetime.strptime(until_local_str, '%Y%m%d')

            local_until_dt = naive_until_dt.replace(tzinfo=dtstart_tz)
            utc_until_dt = local_until_dt.astimezone(ZoneInfo("UTC"))
            utc_until_str_with_z = utc_until_dt.strftime('%Y%m%dT%H%M%SZ')
            
            return rrule_str.replace(non_utc_match.group(0), f'UNTIL={utc_until_str_with_z}')
        except (ValueError, TypeError):
            return rrule_str

    return rrule_str

def parse_and_expand_events(cal, start_range, end_range):
    master_events, overrides, single_events = {}, {}, []

    for component in cal.walk('VEVENT'):
        # --- SỬA LỖI 'NoneType' (1): Bỏ qua sự kiện không có thời gian bắt đầu ---
        if not component.get('dtstart'):
            uid = component.get('uid', 'N/A')
            summary = component.get('summary', 'N/A')
            print(f"Warning: Skipping event (UID: {uid}, Summary: '{summary}') due to missing start time.")
            continue
        # --- KẾT THÚC SỬA LỖI ---
            
        uid = str(component.get('uid'))
        if component.get('recurrence-id'):
            override_date = get_aware_datetime(component.get('recurrence-id'))
            if uid not in overrides: overrides[uid] = {}
            overrides[uid][override_date] = component
        elif component.get('rrule'):
            master_events[uid] = component
        else:
            single_events.append(component)

    all_occurrences = []
    for event in single_events:
        start_dt = get_aware_datetime(event.get('dtstart'))
        if start_range <= start_dt <= end_range:
            processed_event = process_event_to_dict(event, is_recurring=False)
            if processed_event:
                all_occurrences.append(processed_event)

    for uid, master_event in master_events.items():
        rrule_str = master_event.get('rrule').to_ical().decode('utf-8')
        start_dt = get_aware_datetime(master_event.get('dtstart'))
        rrule_str = fix_rrule_until_timezone(rrule_str, start_dt.tzinfo)
        
        # --- SỬA LỖI 'NoneType' (2): Xử lý linh hoạt DURATION / DTEND ---
        # Tính duration từ sự kiện cha một cách an toàn
        master_end_dt = get_aware_datetime(master_event.get('dtend'))
        if master_end_dt:
            duration = master_end_dt - start_dt
        elif master_event.get('duration'):
            duration = master_event.get('duration').dt
        else:
            duration = timedelta(0) # Mặc định là 0 nếu không có cả hai
        # --- KẾT THÚC SỬA LỖI ---

        try:
            rule = rrulestr(rrule_str, dtstart=start_dt)
        except Exception as e:
            print(f"Warning: Could not parse RRULE for event UID {uid}. Skipping. RRULE: '{rrule_str}'. Error: {e}")
            continue

        exdates = set()
        if 'EXDATE' in master_event:
            exdate_prop = master_event.get('exdate')
            if not isinstance(exdate_prop, list): exdate_prop = [exdate_prop]
            for exdate_list in exdate_prop:
                for exdate_val in exdate_list.dts:
                    exdates.add(get_aware_datetime(exdate_val))

        for occurrence_start in rule.between(start_range, end_range, inc=True):
            if occurrence_start in exdates: continue

            instance_event = overrides.get(uid, {}).get(occurrence_start, master_event)
            processed_event = process_event_to_dict(
                instance_event,
                is_recurring=True,
                forced_start_dt=occurrence_start,
                forced_duration=duration if instance_event == master_event else None
            )
            if processed_event:
                all_occurrences.append(processed_event)
                
    return all_occurrences

def process_event_to_dict(event, is_recurring, forced_start_dt=None, forced_duration=None):
    if is_recurring and forced_duration is not None:
        start_dt_aware = forced_start_dt
        end_dt_aware = start_dt_aware + forced_duration
    else:
        start_dt_aware = get_aware_datetime(event.get('dtstart'))
        
        # --- SỬA LỖI 'NoneType' (3): Tìm DTEND hoặc DURATION một cách an toàn ---
        end_dt_aware = get_aware_datetime(event.get('dtend'))
        if not end_dt_aware:
            if event.get('duration'):
                end_dt_aware = start_dt_aware + event.get('duration').dt
            else:
                end_dt_aware = start_dt_aware # Mặc định thời gian kết thúc bằng bắt đầu
        # --- KẾT THÚC SỬA LỖI ---

    start_local = start_dt_aware.astimezone(VIETNAM_TZ)
    end_local = end_dt_aware.astimezone(VIETNAM_TZ)

    organizer_name, organizer_email = "", ""
    if 'organizer' in event:
        organizer_prop = event.get('organizer')
        if isinstance(organizer_prop, str):
            organizer_email = organizer_prop.replace('mailto:', '')
            organizer_name = ""
        else:
            organizer_name = organizer_prop.params.get('CN', '')
            organizer_email = str(organizer_prop).replace('mailto:', '')

    attendees = []
    if 'attendee' in event:
        attendee_list = event.get('attendee')
        if not isinstance(attendee_list, list): attendee_list = [attendee_list]
        for attendee_prop in attendee_list:
            if isinstance(attendee_prop, str):
                email = attendee_prop.replace('mailto:', '')
                name = ""
            else:
                name = attendee_prop.params.get('CN', '')
                email = str(attendee_prop).replace('mailto:', '')
            if name: attendees.append(f"{name} <{email}>")
            else: attendees.append(email)

    return {
        'start_local_date': start_local.strftime('%Y-%m-%d'),
        'start_local_time': start_local.strftime('%H:%M'),
        'end_local_date': end_local.strftime('%Y-%m-%d'),
        'end_local_time': end_local.strftime('%H:%M'),
        'summary': str(event.get('summary', '')),
        'conference_link': extract_conference_link(event),
        'organizer_name': str(organizer_name),
        'organizer_email': str(organizer_email),
        'attendees': "; ".join(attendees),
        'description_plain': clean_description(event.get('description', '')),
        'uid': str(event.get('uid', '')),
        'is_recurring_instance': is_recurring,
    }

def write_csv(events, output_path):
    if not events: return 0
    events.sort(key=lambda x: (x['start_local_date'], x['start_local_time']))

    unique_events = []
    seen = set()
    for event in events:
        unique_key = (event['uid'], event['start_local_date'], event['start_local_time'])
        if unique_key not in seen:
            unique_events.append(event)
            seen.add(unique_key)

    header = [
        'start_local_date', 'start_local_time', 'end_local_date', 'end_local_time',
        'summary', 'conference_link', 'organizer_name', 'organizer_email',
        'attendees', 'description_plain', 'uid', 'is_recurring_instance'
    ]
    with open(output_path, 'w', newline='', encoding='utf-8-sig') as csvfile:
        writer = csv.DictWriter(csvfile, fieldnames=header)
        writer.writeheader()
        writer.writerows(unique_events)
    return len(unique_events)

# ==============================================================================
# PHẦN GIAO DIỆN ĐỒ HỌA (GUI)
# ==============================================================================

class App:
    def __init__(self, root):
        self.root = root
        self.root.title("Công cụ chuyển đổi iCalendar (.ics) sang .csv (v2.1 - Robust)")
        self.root.geometry("600x250")
        self.input_file_path = ""
        self.label_instruction = tk.Label(root, text="Vui lòng chọn file .ics đầu vào và nơi lưu file .csv đầu ra.", pady=10)
        self.label_instruction.pack()
        self.button_select_input = tk.Button(root, text="1. Chọn file .ics...", command=self.select_input_file, width=30, height=2)
        self.button_select_input.pack(pady=5)
        self.label_input_path = tk.Label(root, text="Chưa chọn file nào", fg="blue", wraplength=550)
        self.label_input_path.pack()
        self.button_convert = tk.Button(root, text="2. Chuyển đổi & Lưu file .csv...", command=self.convert_and_save, width=30, height=2, state=tk.DISABLED)
        self.button_convert.pack(pady=10)

    def select_input_file(self):
        file_path = filedialog.askopenfilename(
            title="Chọn file iCalendar",
            filetypes=[("iCalendar files", "*.ics"), ("All files", "*.*")]
        )
        if file_path:
            self.input_file_path = file_path
            self.label_input_path.config(text=f"Đã chọn: {os.path.basename(file_path)}")
            self.button_convert.config(state=tk.NORMAL)

    def convert_and_save(self):
        if not self.input_file_path:
            messagebox.showerror("Lỗi", "Bạn chưa chọn file .ics đầu vào!")
            return

        output_path = filedialog.asksaveasfilename(
            title="Lưu file CSV",
            defaultextension=".csv",
            initialfile=os.path.splitext(os.path.basename(self.input_file_path))[0] + '.csv',
            filetypes=[("CSV files", "*.csv"), ("All files", "*.*")]
        )
        if not output_path: return

        try:
            print("Processing, please wait...")
            now = datetime.now(VIETNAM_TZ)
            start_range = now - timedelta(days=365*20)
            end_range = now + timedelta(days=365*5)

            unfolded_content = unfold_ics_content(self.input_file_path)
            cal = Calendar.from_ical(unfolded_content)
            all_events = parse_and_expand_events(cal, start_range, end_range)
            count = write_csv(all_events, output_path)
            
            print("Processing complete.")
            messagebox.showinfo("Thành công!", f"Đã xử lý và xuất thành công {count} sự kiện ra file:\n{output_path}")

        except Exception as e:
            messagebox.showerror("Đã xảy ra lỗi", f"Không thể xử lý file.\nChi tiết lỗi: {e}")
            traceback.print_exc()

def main():
    root = tk.Tk()
    app = App(root)
    root.mainloop()

if __name__ == "__main__":
    main()
