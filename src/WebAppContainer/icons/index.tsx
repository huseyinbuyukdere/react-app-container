import React from 'react'
import { ReactComponent as api } from './api.svg'
import { ReactComponent as apps } from './apps.svg'
import { ReactComponent as code } from './code.svg'
import { ReactComponent as dashboard } from './dashboard.svg'
import { ReactComponent as home } from './home.svg'
import { ReactComponent as info } from './info.svg'
import { ReactComponent as language } from './language.svg'
import { ReactComponent as list } from './list.svg'
import { ReactComponent as mail } from './mail.svg'
import { ReactComponent as mediation } from './mediation.svg'
import { ReactComponent as message } from './message.svg'
import { ReactComponent as perm_identity } from './perm_identity.svg'
import { ReactComponent as post_add } from './post_add.svg'
import { ReactComponent as radio_button_checked } from './radio_button_checked.svg'
import { ReactComponent as room } from './room.svg'
import { ReactComponent as settings } from './settings.svg'
import { ReactComponent as expand_more} from './expand_more.svg';
import { ReactComponent as expand_less} from './expand_less.svg';

const iconTypes: any = {
    api,
    apps,
    code,
    dashboard,
    home,
    info,
    language,
    list,
    mail,
    mediation,
    message,
    perm_identity,
    post_add,
    radio_button_checked,
    room,
    settings,
    expand_less,
    expand_more
}

interface IconComponentProps {
    name: string
    height?: number
    width?: number
    fill?: string
    className?: string
    style?: any
}

const IconComponent = (props: IconComponentProps) => {
    let Icon = iconTypes[props.name]
    return <Icon className={props.className} {...props} />
}

export default IconComponent
